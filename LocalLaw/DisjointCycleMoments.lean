import LocalLaw.CycleCounting

/-!
# Expected embeddings of vertex-disjoint cycle families

A disjoint family is a single finite degree-two pattern, not a product of
independent cycle events. Its expectation follows from the actual switching
pattern bound. All mixed cycle lengths and their total vertex count are kept.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance disjointCycleDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section DegreeTwo
variable {V : Type*} [Fintype V]

theorem degreeTwo_edgeCount (H : SimpleGraph V) (hdegree : ∀ v, H.degree v = 2) :
    graphEdgeCount H = Fintype.card V := by
  have h := H.sum_degrees_eq_twice_card_edges
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hdegree h
  simp only [hdegree, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id] at h
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at h
  unfold graphEdgeCount
  rw [← Nat.card_eq_fintype_card]
  omega

theorem degreeTwo_degreeProduct (d : ℕ) (H : SimpleGraph V) (hdegree : ∀ v, H.degree v = 2) :
    patternDegreeProduct d H = (d * (d - 1)) ^ Fintype.card V := by
  unfold patternDegreeProduct
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hdegree ⊢
  have htwo : d.descFactorial 2 = d * (d - 1) := by simp [Nat.descFactorial_succ, Nat.mul_comm]
  simp only [hdegree, htwo, Finset.prod_const, Finset.card_univ]
  rw [Nat.card_eq_fintype_card]

end DegreeTwo

/-- Cycle components occupy disjoint sigma-type fibers. -/
def cycleFamilyGraph {I : Type*} (ell : I → ℕ) : SimpleGraph (Σ i, Fin (ell i)) where
  Adj a b := ∃ h : a.1 = b.1, (SimpleGraph.cycleGraph (ell b.1)).Adj (h ▸ a.2) b.2
  symm := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨h, hxy⟩
    cases h
    exact ⟨rfl, hxy.symm⟩
  loopless := by
    rintro ⟨i, x⟩ ⟨h, hxx⟩
    exact (SimpleGraph.cycleGraph (ell i)).loopless x hxx

def cycleFamilyNeighborEquiv {I : Type*} (ell : I → ℕ) (i : I) (v : Fin (ell i)) :
    (SimpleGraph.cycleGraph (ell i)).neighborSet v ≃ (cycleFamilyGraph ell).neighborSet ⟨i, v⟩ :=
  Equiv.ofBijective (fun w => ⟨⟨i, w.val⟩, ⟨rfl, w.property⟩⟩)
    ⟨by
      intro x y h
      apply Subtype.ext
      exact (Sigma.mk.inj_iff.mp (congrArg Subtype.val h)).2.eq,
    by
      rintro ⟨⟨j, w⟩, h, hvw⟩
      cases h
      exact ⟨⟨w, hvw⟩, rfl⟩⟩

theorem cycleFamilyGraph_degree {I : Type*} [Fintype I] (ell : I → ℕ)
    (hell : ∀ i, 3 ≤ ell i) (v : Σ i, Fin (ell i)) :
    (cycleFamilyGraph ell).degree v = 2 := by
  rcases v with ⟨i, x⟩
  have hc := Nat.card_congr (cycleFamilyNeighborEquiv ell i x)
  have hdegree := cycleGraph_degree (ell i) (hell i) x
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hdegree ⊢
  exact hc.symm.trans hdegree

/-- A canonical finite label set allows the checked pattern-count API to
count all disjoint cycle embeddings at once. -/
def finiteCycleFamilyPattern {I : Type*} [Fintype I] (ell : I → ℕ) :
    SimpleGraph (Fin (Fintype.card (Σ i, Fin (ell i)))) :=
  (cycleFamilyGraph ell).map (Fintype.equivFin (Σ i, Fin (ell i))).toEmbedding

theorem finiteCycleFamilyPattern_degree {I : Type*} [Fintype I] (ell : I → ℕ)
    (hell : ∀ i, 3 ≤ ell i) (v : Fin (Fintype.card (Σ i, Fin (ell i)))) :
    (finiteCycleFamilyPattern ell).degree v = 2 := by
  let e := Fintype.equivFin (Σ i, Fin (ell i))
  have h := mappedPattern_degree_image (cycleFamilyGraph ell) e.toEmbedding (e.symm v)
  have hdegree := cycleFamilyGraph_degree ell hell (e.symm v)
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h hdegree ⊢
  simpa only [Equiv.toEmbedding_apply, Equiv.apply_symm_apply] using h.trans hdegree

namespace RegularGraph
variable {N d m : ℕ}

/-- The same sharp expected bound holds for every finite degree-two pattern. -/
theorem expected_degreeTwo_pattern_le_two (H : SimpleGraph (Fin m)) (hdegree : ∀ v, H.degree v = 2)
    (K : ℕ) (hK : m ≤ K) (hKpos : 1 ≤ K) (hN : 0 < N) (hd : 0 < d)
    (hbudget : 2 * K * patternSwitchSlack d K ≤ N * d) :
    (∑ g : RegularGraph N d, weight g * (labelledPatternCount H g.graph : ℝ)) ≤
      2 * (((d - 1 : ℕ) : ℝ) ^ m) := by
  have he := degreeTwo_edgeCount H hdegree
  have hw := degreeTwo_degreeProduct d H hdegree
  have hc := pattern_switching_denominator_control N d K hN hd hKpos hbudget
  let L := N * d - patternSwitchSlack d K
  have hLp : (0 : ℝ) < L := Nat.cast_pos.mpr hc.1
  have hLle : (L : ℝ) ≤ (N : ℝ) * (d : ℝ) := by exact_mod_cast Nat.sub_le (N * d) (patternSwitchSlack d K)
  have hr : 1 ≤ (N : ℝ) * (d : ℝ) / (L : ℝ) :=
    (le_div_iff₀ hLp).mpr (by simpa only [one_mul] using hLle)
  have hinflation : ((N : ℝ) * (d : ℝ) / (L : ℝ)) ^ m ≤ 2 :=
    (pow_le_pow_right₀ hr hK).trans hc.2
  have hbase := expected_labelledPatternCount_power_bound H K L
    (by simpa only [he, Fintype.card_fin] using hK) hc.1 le_rfl
  rw [he, hw] at hbase
  simp only [Fintype.card_fin, Nat.cast_pow, div_pow] at hbase
  calc
    _ ≤ (N : ℝ) ^ m * (((d * (d - 1) : ℕ) : ℝ) / (L : ℝ)) ^ m := by simpa only [div_pow] using hbase
    _ = ((N : ℝ) * (d : ℝ) / (L : ℝ)) ^ m * (((d - 1 : ℕ) : ℝ) ^ m) := by
      rw [← mul_pow, ← mul_pow]
      congr 1
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hinflation (by positivity)

/-- Mixed lengths require no independence: their joint vertex-disjoint
embedding count is bounded as one actual degree-two pattern. -/
theorem expected_disjoint_cycle_family_le_two {I : Type*} [Fintype I]
    (ell : I → ℕ) (hell : ∀ i, 3 ≤ ell i) (K : ℕ) (hK : (∑ i, ell i) ≤ K)
    (hKpos : 1 ≤ K) (hN : 0 < N) (hd : 0 < d)
    (hbudget : 2 * K * patternSwitchSlack d K ≤ N * d) :
    (∑ g : RegularGraph N d, weight g * (labelledPatternCount (finiteCycleFamilyPattern ell) g.graph : ℝ)) ≤
      2 * (((d - 1 : ℕ) : ℝ) ^ (∑ i, ell i)) := by
  have hcard : Fintype.card (Σ i, Fin (ell i)) = ∑ i, ell i := by simp
  have h := expected_degreeTwo_pattern_le_two (finiteCycleFamilyPattern ell)
    (finiteCycleFamilyPattern_degree ell hell) K (by simpa only [hcard] using hK) hKpos hN hd hbudget
  simpa only [hcard] using h


/-- Actual labelled families of q vertex-disjoint cycles of arbitrary lengths
between three and U. This is a finite sum of concrete pattern counts. -/
def packedCycleMoment (q U : ℕ) (G : SimpleGraph (Fin N)) : ℕ :=
  ∑ lengths : Fin q → Fin (U + 1),
    if ∀ i, 3 ≤ (lengths i).val then
      labelledPatternCount (finiteCycleFamilyPattern (fun i => (lengths i).val)) G else 0

/-- A high-moment bound from actual disjoint-pattern counts. The dependence
between cycles is handled by the joint pattern, without independence. -/
theorem expected_packedCycleMoment_bound (q U K : ℕ) (hK : q * U ≤ K)
    (hKpos : 1 ≤ K) (hN : 0 < N) (hd : 2 ≤ d)
    (hbudget : 2 * K * patternSwitchSlack d K ≤ N * d) :
    (∑ g : RegularGraph N d, weight g * (packedCycleMoment q U g.graph : ℝ)) ≤
      2 * ((((U + 1 : ℕ) : ℝ)) * (((d - 1 : ℕ) : ℝ) ^ U)) ^ q := by
  classical
  have hk : (1 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ d - 1 by omega)
  have hlength : ∀ lengths : Fin q → Fin (U + 1), (∑ i, (lengths i).val) ≤ q * U := by
    intro lengths
    calc
      (∑ i, (lengths i).val) ≤ ∑ _i : Fin q, U := Finset.sum_le_sum (fun i _ => by omega)
      _ = q * U := by simp
  have hper : ∀ lengths : Fin q → Fin (U + 1),
      (∑ g : RegularGraph N d, if ∀ i, 3 ≤ (lengths i).val then
        weight g * (labelledPatternCount (finiteCycleFamilyPattern (fun i => (lengths i).val)) g.graph : ℝ)
        else 0) ≤ 2 * (((d - 1 : ℕ) : ℝ) ^ (q * U)) := by
    intro lengths
    by_cases hvalid : ∀ i, 3 ≤ (lengths i).val
    · simp only [if_pos hvalid]
      have h := expected_disjoint_cycle_family_le_two (fun i => (lengths i).val) hvalid
        K ((hlength lengths).trans hK) hKpos hN (by omega) hbudget
      exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hk (hlength lengths)) (by norm_num))
    · simp only [if_neg hvalid, Finset.sum_const_zero]
      positivity
  calc
    _ = ∑ lengths : Fin q → Fin (U + 1), ∑ g : RegularGraph N d,
        if ∀ i, 3 ≤ (lengths i).val then
          weight g * (labelledPatternCount (finiteCycleFamilyPattern (fun i => (lengths i).val)) g.graph : ℝ)
        else 0 := by
      simp only [packedCycleMoment, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero,
        Finset.mul_sum, mul_ite, mul_zero]
      exact Finset.sum_comm
    _ ≤ ∑ _lengths : Fin q → Fin (U + 1), (2 * (((d - 1 : ℕ) : ℝ) ^ (q * U))) :=
      Finset.sum_le_sum (fun lengths _ => hper lengths)
    _ = (((U + 1 : ℕ) : ℝ) ^ q) * (2 * (((d - 1 : ℕ) : ℝ) ^ (q * U))) := by
      simp [nsmul_eq_mul]
    _ = _ := by
      have hp : (((d - 1 : ℕ) : ℝ) ^ (q * U)) = ((((d - 1 : ℕ) : ℝ) ^ U) ^ q) := by
        rw [← pow_mul]
        congr 1
        exact Nat.mul_comm q U
      rw [hp, mul_pow]
      ring

/-- Finite Markov inequality with no normalization assumption. -/
theorem finite_nat_observable_markov {X : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (F : X → ℕ) (t : ℝ) (ht : 0 < t) :
    eventMass w (fun x => t ≤ (F x : ℝ)) ≤ (∑ x, w x * (F x : ℝ)) / t := by
  classical
  apply (le_div_iff₀ ht).mpr
  unfold eventMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : t ≤ (F x : ℝ)
  · simp only [hx, if_true]
    exact mul_le_mul_of_nonneg_left hx (hw x)
  · simp only [hx, if_false, zero_mul]
    exact mul_nonneg (hw x) (Nat.cast_nonneg _)

/-- Explicit upper tail of the actual packed-cycle moment. A deterministic
lower bound for this observable on a graph event can be inserted later. -/
theorem packedCycleMoment_tail (q U K : ℕ) (hK : q * U ≤ K)
    (hKpos : 1 ≤ K) (hN : 0 < N) (hd : 2 ≤ d)
    (hbudget : 2 * K * patternSwitchSlack d K ≤ N * d) (t : ℝ) (ht : 0 < t) :
    eventMass (weight (N := N) (d := d)) (fun g => t ≤ (packedCycleMoment q U g.graph : ℝ)) ≤
      (2 * (((U + 1 : ℕ) : ℝ) * (((d - 1 : ℕ) : ℝ) ^ U)) ^ q) / t := by
  exact (finite_nat_observable_markov weight weight_nonnegative
    (fun g => packedCycleMoment q U g.graph) t ht).trans
    (div_le_div_of_nonneg_right (expected_packedCycleMoment_bound q U K hK hKpos hN hd hbudget) ht.le)

end RegularGraph
end LocalLaw
