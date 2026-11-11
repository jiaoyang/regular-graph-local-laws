import LocalLaw.PatternProbability
import LocalLaw.PatternParameters

/-!
# Expected labelled pattern and cycle embeddings

Every injection gives an actual required-edge pattern on the ambient vertex
set. Mapping preserves its edge count and falling-degree product. Exchanging
the two finite sums converts the pattern probability bound into an expected
embedding count. Cycles of length at least three have degree two and exactly
as many edges as vertices, giving the d(d-1) numerator.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

namespace LocalLaw

local instance cycleCountingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section PatternMaps

variable {V W : Type*} [Fintype V] [Fintype W]

def mappedPatternNeighborEquiv (H : SimpleGraph V) (f : V ↪ W) (v : V) :
    H.neighborSet v ≃ (H.map f).neighborSet (f v) :=
  Equiv.ofBijective
    (fun w => ⟨f w.val, SimpleGraph.map_adj_apply.mpr w.property⟩)
    ⟨by
      intro x y h
      apply Subtype.ext
      exact f.injective (congrArg (fun w : (H.map f).neighborSet (f v) => w.val) h),
    by
      rintro ⟨w, hw⟩
      obtain ⟨x, y, hxy, hx, hy⟩ := (SimpleGraph.map_adj f H (f v) w).mp hw
      have hxv : x = v := f.injective hx
      subst x
      exact ⟨⟨y, hxy⟩, Subtype.ext hy⟩⟩

theorem mappedPattern_degree_image (H : SimpleGraph V) (f : V ↪ W) (v : V) :
    (H.map f).degree (f v) = H.degree v := by
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (mappedPatternNeighborEquiv H f v)).symm

theorem mappedPattern_degree_outside (H : SimpleGraph V) (f : V ↪ W) (w : W)
    (hw : w ∉ Set.range f) : (H.map f).degree w = 0 := by
  letI : IsEmpty ((H.map f).neighborSet w) := ⟨fun u => by
    obtain ⟨x, y, _, hx, _⟩ := (SimpleGraph.map_adj f H w u.val).mp u.property
    exact hw ⟨x, hx⟩⟩
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  simp

/- Mapping an injective pattern creates neither repeated nor extra edges. -/
omit [Fintype V] [Fintype W] in
theorem mappedPattern_edgeCount (H : SimpleGraph V) (f : V ↪ W) :
    graphEdgeCount (H.map f) = graphEdgeCount H := by
  let e := (SimpleGraph.Embedding.map f H).mapEdgeSet
  have hs : Function.Surjective e := by
    rintro ⟨x, hx⟩
    induction x using Sym2.ind with
    | _ x y =>
      change (H.map f).Adj x y at hx
      obtain ⟨u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj f H x y).mp hx
      exact ⟨⟨s(u, v), huv⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective e ⟨e.injective, hs⟩)).symm

/-- Isolated ambient vertices contribute one to the falling-degree product. -/
theorem mappedPattern_degreeProduct (d : ℕ) (H : SimpleGraph V) (f : V ↪ W) :
    patternDegreeProduct d (H.map f) = patternDegreeProduct d H := by
  let R : Finset W := Finset.univ.image f
  have himage : ∀ w : W, w ∈ R ↔ w ∈ Set.range f := by
    intro w
    simp only [R, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]
  have hprod : (∏ w : W, d.descFactorial ((H.map f).degree w)) =
      ∏ w ∈ R, d.descFactorial ((H.map f).degree w) := by
    symm
    apply Finset.prod_subset (Finset.subset_univ R)
    intro w _ hw
    rw [mappedPattern_degree_outside H f w (fun h => hw ((himage w).mpr h)),
      Nat.descFactorial_zero]
  have hpoint : ∀ v, d.descFactorial ((H.map f).degree (f v)) =
      d.descFactorial (H.degree v) := fun v => congrArg (Nat.descFactorial d)
        (mappedPattern_degree_image H f v)
  unfold patternDegreeProduct
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    at hprod hpoint ⊢
  rw [hprod]
  unfold R
  rw [Finset.prod_image (fun x _ y _ h => f.injective h)]
  exact Finset.prod_congr rfl (fun v _ => hpoint v)

omit [Fintype V] [Fintype W] in
theorem mappedPattern_le_iff (H : SimpleGraph V) (f : V ↪ W) (G : SimpleGraph W) :
    H.map f ≤ G ↔ ∀ v w, H.Adj v w → G.Adj (f v) (f w) := by
  constructor
  · intro h v w hvw
    exact h (SimpleGraph.map_adj_apply.mpr hvw)
  · intro h x y hxy
    obtain ⟨u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj f H x y).mp hxy
    exact h u v huv

end PatternMaps

/-- Actual labelled, injective, edge-preserving embeddings of H in G. -/
def labelledPatternCount {m N : ℕ} (H : SimpleGraph (Fin m)) (G : SimpleGraph (Fin N)) : ℕ :=
  (Finset.univ.filter (fun f : Fin m ↪ Fin N => H.map f ≤ G)).card

namespace RegularGraph

variable {N degree m : ℕ}

/-- Exchange the finite graph and embedding sums; no independence is used. -/
theorem expected_labelledPatternCount_eq (H : SimpleGraph (Fin m)) :
    (∑ g : RegularGraph N degree, weight g * (labelledPatternCount H g.graph : ℝ)) =
      ∑ f : Fin m ↪ Fin N, eventMass (weight (N := N) (d := degree))
        (fun g => H.map f ≤ g.graph) := by
  have hcount : ∀ g : RegularGraph N degree,
      (labelledPatternCount H g.graph : ℝ) =
        ∑ f : Fin m ↪ Fin N, if H.map f ≤ g.graph then (1 : ℝ) else 0 := by
    intro g
    rw [← Finset.sum_filter]
    simp [labelledPatternCount]
  calc
    _ = ∑ g : RegularGraph N degree, ∑ f : Fin m ↪ Fin N,
        if H.map f ≤ g.graph then weight g else 0 := by
      apply Finset.sum_congr rfl
      intro g _
      rw [hcount g, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      split_ifs <;> simp
    _ = ∑ f : Fin m ↪ Fin N, ∑ g : RegularGraph N degree,
        if H.map f ≤ g.graph then weight g else 0 := Finset.sum_comm
    _ = _ := rfl

/-- Generic expected labelled-pattern bound with its exact falling-degree numerator. -/
theorem expected_labelledPatternCount_bound (H : SimpleGraph (Fin m)) (K L : ℕ)
    (hK : graphEdgeCount H ≤ K) (hL : 0 < L)
    (hbudget : L ≤ N * degree - patternSwitchSlack degree K) :
    (∑ g : RegularGraph N degree, weight g * (labelledPatternCount H g.graph : ℝ)) ≤
      (Fintype.card (Fin m ↪ Fin N) : ℝ) *
        ((patternDegreeProduct degree H : ℝ) / (L : ℝ) ^ graphEdgeCount H) := by
  rw [expected_labelledPatternCount_eq]
  calc
    _ ≤ ∑ _f : Fin m ↪ Fin N,
        ((patternDegreeProduct degree H : ℝ) / (L : ℝ) ^ graphEdgeCount H) := by
      apply Finset.sum_le_sum
      intro f _
      have hp := pattern_probability_bound (H.map f) K L
        (by simpa only [mappedPattern_edgeCount] using hK) hL hbudget
      simpa only [mappedPattern_edgeCount, mappedPattern_degreeProduct] using hp
    _ = _ := by simp

theorem injection_card_le_power (m N : ℕ) : Fintype.card (Fin m ↪ Fin N) ≤ N ^ m := by
  have h := Fintype.card_le_of_injective (fun f : Fin m ↪ Fin N => (f : Fin m → Fin N))
    Function.Embedding.coe_injective
  simpa using h

theorem expected_labelledPatternCount_power_bound (H : SimpleGraph (Fin m)) (K L : ℕ)
    (hK : graphEdgeCount H ≤ K) (hL : 0 < L)
    (hbudget : L ≤ N * degree - patternSwitchSlack degree K) :
    (∑ g : RegularGraph N degree, weight g * (labelledPatternCount H g.graph : ℝ)) ≤
      (N : ℝ) ^ m * ((patternDegreeProduct degree H : ℝ) /
        (L : ℝ) ^ graphEdgeCount H) := by
  apply (expected_labelledPatternCount_bound H K L hK hL hbudget).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast injection_card_le_power m N

end RegularGraph

theorem cycleGraph_degree (ell : ℕ) (hell : 3 ≤ ell) (v : Fin ell) :
    (SimpleGraph.cycleGraph ell).degree v = 2 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hell
  have heq : ell = k + 3 := by omega
  clear hk
  subst ell
  exact SimpleGraph.cycleGraph_degree_three_le

/-- A cycle of length at least three has exactly ell undirected edges. -/
theorem cycleGraph_edgeCount (ell : ℕ) (hell : 3 ≤ ell) :
    graphEdgeCount (SimpleGraph.cycleGraph ell) = ell := by
  have h := (SimpleGraph.cycleGraph ell).sum_degrees_eq_twice_card_edges
  have hdegree := cycleGraph_degree ell hell
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    at hdegree h
  simp only [hdegree, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id] at h
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at h
  unfold graphEdgeCount
  omega

/-- The exact cycle numerator d(d-1) per labelled vertex. -/
theorem cycleGraph_degreeProduct (d ell : ℕ) (hell : 3 ≤ ell) :
    patternDegreeProduct d (SimpleGraph.cycleGraph ell) = (d * (d - 1)) ^ ell := by
  have hdegree := cycleGraph_degree ell hell
  unfold patternDegreeProduct
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    at hdegree ⊢
  have htwo : d.descFactorial 2 = d * (d - 1) := by
    simp [Nat.descFactorial_succ, Nat.mul_comm]
  simp only [hdegree, htwo, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The actual required cycle-edge pattern on ambient vertices. -/
def cyclePattern {ell N : ℕ} (f : Fin ell ↪ Fin N) : SimpleGraph (Fin N) :=
  (SimpleGraph.cycleGraph ell).map f

theorem cyclePattern_edgeCount {ell N : ℕ} (hell : 3 ≤ ell) (f : Fin ell ↪ Fin N) :
    graphEdgeCount (cyclePattern f) = ell := by
  rw [cyclePattern, mappedPattern_edgeCount, cycleGraph_edgeCount ell hell]

theorem cyclePattern_degree_image {ell N : ℕ} (hell : 3 ≤ ell)
    (f : Fin ell ↪ Fin N) (v : Fin ell) : (cyclePattern f).degree (f v) = 2 := by
  have hm := mappedPattern_degree_image (SimpleGraph.cycleGraph ell) f v
  have hc := cycleGraph_degree ell hell v
  simp only [cyclePattern, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at hm hc ⊢
  exact hm.trans hc

theorem cyclePattern_degree_outside {ell N : ℕ} (f : Fin ell ↪ Fin N)
    (v : Fin N) (hv : v ∉ Set.range f) : (cyclePattern f).degree v = 0 := by
  have h := mappedPattern_degree_outside (SimpleGraph.cycleGraph ell) f v hv
  simp only [cyclePattern, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at h ⊢
  exact h

theorem cyclePattern_degreeProduct (d : ℕ) {ell N : ℕ} (hell : 3 ≤ ell)
    (f : Fin ell ↪ Fin N) :
    patternDegreeProduct d (cyclePattern f) = (d * (d - 1)) ^ ell := by
  rw [cyclePattern, mappedPattern_degreeProduct, cycleGraph_degreeProduct d ell hell]

/-- This counts all starting labels and both orientations of each simple cycle. -/
def labelledCycleCount {N : ℕ} (ell : ℕ) (G : SimpleGraph (Fin N)) : ℕ :=
  labelledPatternCount (SimpleGraph.cycleGraph ell) G

namespace RegularGraph

variable {N degree ell : ℕ}

/-- Expected number of actual labelled injective cycle embeddings. -/
theorem expected_labelledCycleCount_bound (hell : 3 ≤ ell) (K L : ℕ)
    (hK : ell ≤ K) (hL : 0 < L)
    (hbudget : L ≤ N * degree - patternSwitchSlack degree K) :
    (∑ g : RegularGraph N degree, weight g * (labelledCycleCount ell g.graph : ℝ)) ≤
      (Fintype.card (Fin ell ↪ Fin N) : ℝ) *
        (((degree * (degree - 1) : ℕ) : ℝ) / (L : ℝ)) ^ ell := by
  have h := expected_labelledPatternCount_bound (SimpleGraph.cycleGraph ell) K L
    (by simpa only [cycleGraph_edgeCount ell hell] using hK) hL hbudget
  simpa only [labelledCycleCount, cycleGraph_edgeCount ell hell,
    cycleGraph_degreeProduct degree ell hell, Nat.cast_pow, div_pow] using h

/-- Coarse embedding count N^ell with the sharp d(d-1) cycle numerator. -/
theorem expected_labelledCycleCount_power_bound (hell : 3 ≤ ell) (K L : ℕ)
    (hK : ell ≤ K) (hL : 0 < L)
    (hbudget : L ≤ N * degree - patternSwitchSlack degree K) :
    (∑ g : RegularGraph N degree, weight g * (labelledCycleCount ell g.graph : ℝ)) ≤
      (((N : ℝ) * ((degree * (degree - 1) : ℕ) : ℝ)) / (L : ℝ)) ^ ell := by
  apply (expected_labelledCycleCount_bound hell K L hK hL hbudget).trans
  have hcard : (Fintype.card (Fin ell ↪ Fin N) : ℝ) ≤ (N : ℝ) ^ ell := by
    exact_mod_cast injection_card_le_power ell N
  calc
    _ ≤ (N : ℝ) ^ ell *
        (((degree * (degree - 1) : ℕ) : ℝ) / (L : ℝ)) ^ ell :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

/-- Numerical control of the actual switching denominator gives a constant
factor two, without changing the (d-1)^ell cycle growth rate. -/
theorem expected_labelledCycleCount_le_two (hell : 3 ≤ ell) (K : ℕ)
    (hK : ell ≤ K) (hN : 0 < N) (hd : 0 < degree)
    (hbudget : 2 * K * patternSwitchSlack degree K ≤ N * degree) :
    (∑ g : RegularGraph N degree, weight g * (labelledCycleCount ell g.graph : ℝ)) ≤
      2 * (((degree - 1 : ℕ) : ℝ) ^ ell) := by
  have hKpos : 1 ≤ K := by omega
  have hc := pattern_switching_denominator_control N degree K hN hd hKpos hbudget
  let L := N * degree - patternSwitchSlack degree K
  have hLp : (0 : ℝ) < L := Nat.cast_pos.mpr hc.1
  have hLle : (L : ℝ) ≤ (N : ℝ) * (degree : ℝ) := by
    exact_mod_cast (Nat.sub_le (N * degree) (patternSwitchSlack degree K))
  have hratio : 1 ≤ ((N : ℝ) * (degree : ℝ)) / (L : ℝ) := by
    apply (le_div_iff₀ hLp).mpr
    simpa only [one_mul] using hLle
  have hinflation : (((N : ℝ) * (degree : ℝ)) / (L : ℝ)) ^ ell ≤ 2 :=
    (pow_le_pow_right₀ hratio hK).trans hc.2
  have hbase := expected_labelledCycleCount_power_bound hell K L hK hc.1 le_rfl
  apply hbase.trans
  have hidentity : ((N : ℝ) * ((degree * (degree - 1) : ℕ) : ℝ)) / (L : ℝ) =
      (((N : ℝ) * (degree : ℝ)) / (L : ℝ)) * ((degree - 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hidentity, mul_pow]
  exact mul_le_mul_of_nonneg_right hinflation (by positivity)

end RegularGraph

end LocalLaw
