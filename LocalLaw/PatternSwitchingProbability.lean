import LocalLaw.ExcessCutset

/-!
# Inclusion of a sparse required-edge pattern under the regular-graph law

The switching count keeps the residual degrees at the two target endpoints.
Forward data are actual admissible simple switchings which remove the target
edge without deleting a required edge. Their images are encoded by the switched
graph and two neighbors outside the required pattern. The inverse switching
proves injectivity of this encoding.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000

namespace LocalLaw

local instance patternSwitchDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section FiniteCounting

variable {Ω : Type*} [Fintype Ω]

/-- Counting a cover by four events, without any disjointness requirement. -/
theorem finite_four_cover_card (P Q R S : Ω → Prop)
    (hcover : ∀ ω, P ω ∨ Q ω ∨ R ω ∨ S ω) :
    Nat.card Ω ≤ Nat.card {ω // P ω} + Nat.card {ω // Q ω} +
      Nat.card {ω // R ω} + Nat.card {ω // S ω} := by
  classical
  let A := Finset.univ.filter P
  let B := Finset.univ.filter Q
  let C := Finset.univ.filter R
  let D := Finset.univ.filter S
  have hsub : (Finset.univ : Finset Ω) ⊆ ((A ∪ B) ∪ C) ∪ D := by
    intro ω _
    simpa only [A, B, C, D, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, or_assoc] using hcover ω
  have h := Finset.card_le_card hsub
  have hab := Finset.card_union_le A B
  have habc := Finset.card_union_le (A ∪ B) C
  have habcd := Finset.card_union_le ((A ∪ B) ∪ C) D
  have hA : A.card = Nat.card {ω // P ω} := by
    simp only [A, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hB : B.card = Nat.card {ω // Q ω} := by
    simp only [B, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hC : C.card = Nat.card {ω // R ω} := by
    simp only [C, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hD : D.card = Nat.card {ω // S ω} := by
    simp only [D, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h
  omega

end FiniteCounting

section SwitchingPreservation

variable {V : Type*} (S G : SimpleGraph V) (a b c d : V)

/-- A switching preserves all required edges if neither removed edge is required. -/
theorem required_pattern_le_switch (hSG : S ≤ G)
    (hab : ¬ S.Adj a b) (hcd : ¬ S.Adj c d) :
    S ≤ simpleSwitch G a b c d := by
  have hdis : Disjoint S (switchingRemoved a b c d) :=
    disjoint_sup_right.mpr ⟨(S.disjoint_edge).mpr hab, (S.disjoint_edge).mpr hcd⟩
  exact le_sup_of_le_left (le_sdiff.mpr ⟨hSG, hdis⟩)

theorem required_sup_edge_iff (hab : a ≠ b) :
    S ⊔ SimpleGraph.edge a b ≤ G ↔ S ≤ G ∧ G.Adj a b := by
  constructor
  · intro h
    refine ⟨le_trans le_sup_left h, ?_⟩
    apply h
    exact Or.inr (by simp [SimpleGraph.edge_adj, hab])
  · rintro ⟨hSG, hadj⟩
    exact sup_le hSG (sup_eq_left.mp (G.sup_edge_of_adj hadj))

end SwitchingPreservation

namespace RegularGraph

variable {N degree : ℕ}

/-- Regular graphs containing every edge of S. -/
def PatternClass (S : SimpleGraph (Fin N)) :=
  {g : RegularGraph N degree // S ≤ g.graph}

def PatternPresent (S : SimpleGraph (Fin N)) (a b : Fin N) :=
  {g : RegularGraph N degree // S ≤ g.graph ∧ g.graph.Adj a b}

def PatternAbsent (S : SimpleGraph (Fin N)) (a b : Fin N) :=
  {g : RegularGraph N degree // S ≤ g.graph ∧ ¬g.graph.Adj a b}

instance patternClassFintype (S : SimpleGraph (Fin N)) : Fintype (PatternClass (degree := degree) S) := by
  unfold PatternClass
  infer_instance

instance patternPresentFintype (S : SimpleGraph (Fin N)) (a b : Fin N) :
    Fintype (PatternPresent (degree := degree) S a b) := by
  unfold PatternPresent
  infer_instance

instance patternAbsentFintype (S : SimpleGraph (Fin N)) (a b : Fin N) :
    Fintype (PatternAbsent (degree := degree) S a b) := by
  unfold PatternAbsent
  infer_instance

/-- A neighbor available for the inverse switching, outside the required pattern. -/
def ResidualNeighbor (g : RegularGraph N degree) (S : SimpleGraph (Fin N)) (v : Fin N) :=
  {w : Fin N // g.graph.Adj v w ∧ ¬S.Adj v w}

instance residualNeighborFintype (g : RegularGraph N degree) (S : SimpleGraph (Fin N))
    (v : Fin N) : Fintype (ResidualNeighbor g S v) := by
  unfold ResidualNeighbor
  infer_instance

/-- Exactly the residual degree is available, rather than a coarse bound by d. -/
theorem residualNeighbor_card (g : RegularGraph N degree) (S : SimpleGraph (Fin N))
    (hSG : S ≤ g.graph) (v : Fin N) :
    Nat.card (ResidualNeighbor g S v) = degree - S.degree v := by
  let e : ResidualNeighbor g S v ≃
      {w // w ∈ g.graph.neighborFinset v \ S.neighborFinset v} :=
    { toFun := fun w => ⟨w.val, by simpa only [Finset.mem_sdiff,
        SimpleGraph.mem_neighborFinset, and_comm] using w.property⟩
      invFun := fun w => ⟨w.val, by simpa only [Finset.mem_sdiff,
        SimpleGraph.mem_neighborFinset, and_comm] using w.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsub : S.neighborFinset v ⊆ g.graph.neighborFinset v := by
    intro w hw
    exact (g.graph.mem_neighborFinset v w).mpr (hSG ((S.mem_neighborFinset v w).mp hw))
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_sdiff hsub]
  simp only [SimpleGraph.card_neighborFinset_eq_degree, g.regular v]

/-- All oriented edges satisfying the forward simple-switch conditions. -/
def PatternForwardChoice (S : SimpleGraph (Fin N)) (a b : Fin N)
    (g : PatternPresent (degree := degree) S a b) :=
  {e : g.val.graph.Dart //
    SimpleSwitchingAdmissible g.val.graph a b e.fst e.snd ∧ ¬S.Adj e.fst e.snd}

instance patternForwardChoiceFintype (S : SimpleGraph (Fin N)) (a b : Fin N)
    (g : PatternPresent (degree := degree) S a b) : Fintype (PatternForwardChoice S a b g) := by
  unfold PatternForwardChoice
  infer_instance

/-- The deliberately explicit finite forward loss budget. -/
def patternSwitchSlack (degree edges : ℕ) : ℕ := 2 * degree * (degree + 2) + 2 * edges

theorem dart_first_fiber_bound (g : RegularGraph N degree) (v : Fin N) :
    Nat.card {e : g.graph.Dart // e.fst = v} ≤ degree := by
  let f : {e : g.graph.Dart // e.fst = v} → g.graph.neighborSet v :=
    fun e => ⟨e.val.snd, by simpa only [e.property] using e.val.adj⟩
  have hf : Function.Injective f := by
    intro e f' h
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    exact Prod.ext (e.property.trans f'.property.symm)
      (congrArg (fun w : g.graph.neighborSet v => w.val) h)
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree,
    g.regular v] using h

theorem dart_second_fiber_bound (g : RegularGraph N degree) (v : Fin N) :
    Nat.card {e : g.graph.Dart // e.snd = v} ≤ degree := by
  let f : {e : g.graph.Dart // e.snd = v} → g.graph.neighborSet v :=
    fun e => ⟨e.val.fst, by simpa only [e.property] using e.val.adj.symm⟩
  have hf : Function.Injective f := by
    intro e f' h
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    exact Prod.ext (congrArg (fun w : g.graph.neighborSet v => w.val) h)
      (e.property.trans f'.property.symm)
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree,
    g.regular v] using h

theorem required_dart_count_bound (g : RegularGraph N degree) (S : SimpleGraph (Fin N)) :
    Nat.card {e : g.graph.Dart // S.Adj e.fst e.snd} ≤ 2 * graphEdgeCount S := by
  let f : {e : g.graph.Dart // S.Adj e.fst e.snd} → S.Dart :=
    fun e => ⟨e.val.toProd, e.property⟩
  have hf : Function.Injective f := by
    intro e f' h
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    exact congrArg (fun w : S.Dart => w.toProd) h
  exact (Nat.card_le_card_of_injective f hf).trans_eq (graph_dart_count S)

/-- Count all excluded darts by two endpoint neighborhoods and the required
edges. This is the actual forward switching lower bound. -/
theorem patternForwardChoice_card_lower (S : SimpleGraph (Fin N)) (a b : Fin N)
    (g : PatternPresent (degree := degree) S a b) :
    N * degree - patternSwitchSlack degree (graphEdgeCount S) ≤
      Nat.card (PatternForwardChoice S a b g) := by
  let leftBad := insert a (insert b (g.val.graph.neighborFinset b))
  let rightBad := insert a (insert b (g.val.graph.neighborFinset a))
  have hleftSize : leftBad.card ≤ degree + 2 := by
    change (insert a (insert b (g.val.graph.neighborFinset b))).card ≤ degree + 2
    have h₁ := Finset.card_insert_le a (insert b (g.val.graph.neighborFinset b))
    have h₂ := Finset.card_insert_le b (g.val.graph.neighborFinset b)
    simp only [SimpleGraph.card_neighborFinset_eq_degree, g.val.regular b] at h₂
    omega
  have hrightSize : rightBad.card ≤ degree + 2 := by
    change (insert a (insert b (g.val.graph.neighborFinset a))).card ≤ degree + 2
    have h₁ := Finset.card_insert_le a (insert b (g.val.graph.neighborFinset a))
    have h₂ := Finset.card_insert_le b (g.val.graph.neighborFinset a)
    simp only [SimpleGraph.card_neighborFinset_eq_degree, g.val.regular a] at h₂
    omega
  have hleft := endpoint_preimage_card_bound (fun e : g.val.graph.Dart => e.fst)
    leftBad degree g.val.dart_first_fiber_bound
  have hright := endpoint_preimage_card_bound (fun e : g.val.graph.Dart => e.snd)
    rightBad degree g.val.dart_second_fiber_bound
  change Nat.card {e : g.val.graph.Dart // e.fst ∈ leftBad} ≤ leftBad.card * degree at hleft
  change Nat.card {e : g.val.graph.Dart // e.snd ∈ rightBad} ≤ rightBad.card * degree at hright
  have hrequired := g.val.required_dart_count_bound S
  have hcover : ∀ e : g.val.graph.Dart,
      (SimpleSwitchingAdmissible g.val.graph a b e.fst e.snd ∧ ¬S.Adj e.fst e.snd) ∨
      e.fst ∈ leftBad ∨ e.snd ∈ rightBad ∨ S.Adj e.fst e.snd := by
    intro e
    by_cases hl : e.fst ∈ leftBad
    · exact Or.inr (Or.inl hl)
    by_cases hr : e.snd ∈ rightBad
    · exact Or.inr (Or.inr (Or.inl hr))
    by_cases hs : S.Adj e.fst e.snd
    · exact Or.inr (Or.inr (Or.inr hs))
    have hlf : e.fst ≠ a ∧ e.fst ≠ b ∧ ¬g.val.graph.Adj b e.fst := by
      simpa only [leftBad, Finset.mem_insert, SimpleGraph.mem_neighborFinset,
        not_or] using hl
    have hrf : e.snd ≠ a ∧ e.snd ≠ b ∧ ¬g.val.graph.Adj a e.snd := by
      simpa only [rightBad, Finset.mem_insert, SimpleGraph.mem_neighborFinset,
        not_or] using hr
    exact Or.inl ⟨⟨g.property.2.ne, hlf.1.symm, hrf.1.symm, hlf.2.1.symm,
      hrf.2.1.symm, e.adj.ne, g.property.2, e.adj, hrf.2.2, hlf.2.2⟩, hs⟩
  have hcount := finite_four_cover_card _ _ _ _ hcover
  rw [g.val.oriented_edge_count] at hcount
  have hl := Nat.mul_le_mul_right degree hleftSize
  have hr := Nat.mul_le_mul_right degree hrightSize
  change N * degree - patternSwitchSlack degree (graphEdgeCount S) ≤
    Nat.card {e : g.val.graph.Dart //
      SimpleSwitchingAdmissible g.val.graph a b e.fst e.snd ∧ ¬S.Adj e.fst e.snd}
  unfold patternSwitchSlack
  have hslack : 2 * degree * (degree + 2) = 2 * ((degree + 2) * degree) := by ring
  omega

/-- The actual switched regular graph. -/
def patternSwitchedGraph (S : SimpleGraph (Fin N)) (a b : Fin N)
    (g : PatternPresent (degree := degree) S a b) (e : PatternForwardChoice S a b g) :
    RegularGraph N degree :=
  ⟨simpleSwitch g.val.graph a b e.val.fst e.val.snd,
    e.property.1.regular g.val.regular⟩

/-- The target edge has been removed, and all required edges survive. -/
def patternSwitchOutput (S : SimpleGraph (Fin N)) (a b : Fin N) (hab : ¬S.Adj a b)
    (g : PatternPresent (degree := degree) S a b) (e : PatternForwardChoice S a b g) :
    PatternAbsent (degree := degree) S a b :=
  ⟨patternSwitchedGraph S a b g e,
    required_pattern_le_switch S g.val.graph a b e.val.fst e.val.snd
      g.property.1 hab e.property.2,
    e.property.1.inverse_admissible.new_ad⟩

/-- Forward data are encoded by the output graph and its two residual neighbors. -/
def patternSwitchEncoding (S : SimpleGraph (Fin N)) (a b : Fin N) (hab : ¬S.Adj a b) :
    (Σ g : PatternPresent (degree := degree) S a b, PatternForwardChoice S a b g) →
      Σ h : PatternAbsent (degree := degree) S a b,
        ResidualNeighbor h.val S a × ResidualNeighbor h.val S b := fun p =>
  ⟨patternSwitchOutput S a b hab p.1 p.2,
    ⟨⟨p.2.val.snd, (p.2.property.1.adj_a _).mpr (Or.inr rfl),
      fun hs => p.2.property.1.new_ad (p.1.property.1 hs)⟩,
      ⟨p.2.val.fst, (p.2.property.1.adj_b _).mpr (Or.inr rfl),
        fun hs => p.2.property.1.new_bc (p.1.property.1 hs)⟩⟩⟩

/-- The inverse simple switching reconstructs the input graph and sampled dart. -/
theorem patternSwitchEncoding_injective (S : SimpleGraph (Fin N)) (a b : Fin N)
    (hab : ¬S.Adj a b) :
    Function.Injective (patternSwitchEncoding (degree := degree) S a b hab) := by
  rintro ⟨g, e⟩ ⟨g', e'⟩ heq
  have hc : e.val.fst = e'.val.fst :=
    congrArg (fun p : Σ h : PatternAbsent (degree := degree) S a b,
      ResidualNeighbor h.val S a × ResidualNeighbor h.val S b => p.2.2.val) heq
  have hd : e.val.snd = e'.val.snd :=
    congrArg (fun p : Σ h : PatternAbsent (degree := degree) S a b,
      ResidualNeighbor h.val S a × ResidualNeighbor h.val S b => p.2.1.val) heq
  have hH : simpleSwitch g.val.graph a b e.val.fst e.val.snd =
      simpleSwitch g'.val.graph a b e'.val.fst e'.val.snd :=
    congrArg (fun p : Σ h : PatternAbsent (degree := degree) S a b,
      ResidualNeighbor h.val S a × ResidualNeighbor h.val S b => p.1.val.graph) heq
  have hG : g.val.graph = g'.val.graph := by
    calc
      g.val.graph = simpleSwitch (simpleSwitch g.val.graph a b e.val.fst e.val.snd)
          a e.val.snd e.val.fst b := e.property.1.switch_inverse.symm
      _ = simpleSwitch (simpleSwitch g'.val.graph a b e'.val.fst e'.val.snd)
          a e'.val.snd e'.val.fst b := by rw [hH, hc, hd]
      _ = g'.val.graph := e'.property.1.switch_inverse
  have hgval : g.val = g'.val := Subtype.ext hG
  have hg : g = g' := Subtype.ext hgval
  cases hg
  have he : e = e' := by
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    exact Prod.ext hc hd
  cases he
  rfl

theorem pattern_forward_total_lower (S : SimpleGraph (Fin N)) (a b : Fin N) :
    Nat.card (PatternPresent (degree := degree) S a b) *
        (N * degree - patternSwitchSlack degree (graphEdgeCount S)) ≤
      Nat.card (Σ g : PatternPresent (degree := degree) S a b, PatternForwardChoice S a b g) := by
  calc
    _ = ∑ _g : PatternPresent (degree := degree) S a b,
        (N * degree - patternSwitchSlack degree (graphEdgeCount S)) := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ ∑ g : PatternPresent (degree := degree) S a b,
        Nat.card (PatternForwardChoice S a b g) :=
      Finset.sum_le_sum (fun g _ => patternForwardChoice_card_lower S a b g)
    _ = _ := Nat.card_sigma.symm

theorem pattern_reverse_encoding_card (S : SimpleGraph (Fin N)) (a b : Fin N) :
    Nat.card (Σ h : PatternAbsent (degree := degree) S a b,
      ResidualNeighbor h.val S a × ResidualNeighbor h.val S b) =
        Nat.card (PatternAbsent (degree := degree) S a b) *
          ((degree - S.degree a) * (degree - S.degree b)) := by
  rw [Nat.card_sigma]
  calc
    _ = ∑ _h : PatternAbsent (degree := degree) S a b,
        ((degree - S.degree a) * (degree - S.degree b)) := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Nat.card_prod, residualNeighbor_card h.val S h.property.1 a,
        residualNeighbor_card h.val S h.property.1 b]
    _ = _ := by
      simp [Nat.card_eq_fintype_card]

/-- The actual finite switching inequality, with the endpoint residual degrees
retained. No extension-count or probability estimate is an assumption. -/
theorem pattern_switching_count (S : SimpleGraph (Fin N)) (a b : Fin N)
    (hab : ¬S.Adj a b) :
    Nat.card (PatternPresent (degree := degree) S a b) *
        (N * degree - patternSwitchSlack degree (graphEdgeCount S)) ≤
      Nat.card (PatternAbsent (degree := degree) S a b) *
        ((degree - S.degree a) * (degree - S.degree b)) := by
  have hinj := Nat.card_le_card_of_injective (patternSwitchEncoding S a b hab)
    (patternSwitchEncoding_injective (degree := degree) S a b hab)
  exact (pattern_forward_total_lower S a b).trans
    (hinj.trans_eq (pattern_reverse_encoding_card S a b))

/-- For d≥2 the explicit slack is at most 4d²+2|E(S)|. -/
theorem pattern_switching_count_square_slack (S : SimpleGraph (Fin N)) (a b : Fin N)
    (hab : ¬S.Adj a b) (hd : 2 ≤ degree) :
    Nat.card (PatternPresent (degree := degree) S a b) *
        (N * degree - (4 * degree ^ 2 + 2 * graphEdgeCount S)) ≤
      Nat.card (PatternAbsent (degree := degree) S a b) *
        ((degree - S.degree a) * (degree - S.degree b)) := by
  have hslack : patternSwitchSlack degree (graphEdgeCount S) ≤
      4 * degree ^ 2 + 2 * graphEdgeCount S := by
    unfold patternSwitchSlack
    nlinarith
  exact (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hslack (N * degree))).trans
    (pattern_switching_count S a b hab)

/-- Splitting the conditioned ensemble according to the target edge. -/
def patternPartitionEquiv (S : SimpleGraph (Fin N)) (a b : Fin N) :
    PatternClass (degree := degree) S ≃
      PatternPresent (degree := degree) S a b ⊕ PatternAbsent (degree := degree) S a b where
  toFun g := if h : g.val.graph.Adj a b then Sum.inl ⟨g.val, g.property, h⟩
    else Sum.inr ⟨g.val, g.property, h⟩
  invFun
    | Sum.inl g => ⟨g.val, g.property.1⟩
    | Sum.inr g => ⟨g.val, g.property.1⟩
  left_inv g := by by_cases h : g.val.graph.Adj a b <;> simp [h]
  right_inv g := by
    cases g with
    | inl g => simp [g.property.2]
    | inr g => simp [g.property.2]

theorem pattern_class_card_partition (S : SimpleGraph (Fin N)) (a b : Fin N) :
    Nat.card (PatternClass (degree := degree) S) =
      Nat.card (PatternPresent (degree := degree) S a b) +
        Nat.card (PatternAbsent (degree := degree) S a b) := by
  rw [Nat.card_congr (patternPartitionEquiv (degree := degree) S a b), Nat.card_sum]

/-- Conditional inclusion probability in cardinal form; it is also defined
as zero when the required pattern has no regular-graph completion. -/
theorem pattern_conditional_card_probability (S : SimpleGraph (Fin N)) (a b : Fin N)
    (hab : ¬S.Adj a b)
    (hpositive : 0 < N * degree - patternSwitchSlack degree (graphEdgeCount S)) :
    (Nat.card (PatternPresent (degree := degree) S a b) : ℝ) /
        (Nat.card (PatternClass (degree := degree) S) : ℝ) ≤
      ((degree - S.degree a : ℕ) : ℝ) * ((degree - S.degree b : ℕ) : ℝ) /
        ((N * degree - patternSwitchSlack degree (graphEdgeCount S) : ℕ) : ℝ) := by
  have hcount := pattern_switching_count (degree := degree) S a b hab
  have hpartition := pattern_class_card_partition (degree := degree) S a b
  have hL : (0 : ℝ) < (N * degree - patternSwitchSlack degree (graphEdgeCount S) : ℕ) :=
    Nat.cast_pos.mpr hpositive
  have hcountR : (Nat.card (PatternPresent (degree := degree) S a b) : ℝ) *
      ((N * degree - patternSwitchSlack degree (graphEdgeCount S) : ℕ) : ℝ) ≤
        (Nat.card (PatternAbsent (degree := degree) S a b) : ℝ) *
          (((degree - S.degree a : ℕ) : ℝ) * ((degree - S.degree b : ℕ) : ℝ)) := by
    exact_mod_cast hcount
  have hpartitionR : (Nat.card (PatternClass (degree := degree) S) : ℝ) =
      (Nat.card (PatternPresent (degree := degree) S a b) : ℝ) +
        (Nat.card (PatternAbsent (degree := degree) S a b) : ℝ) := by exact_mod_cast hpartition
  by_cases hC : 0 < Nat.card (PatternClass (degree := degree) S)
  · apply (div_le_div_iff₀ (Nat.cast_pos.mpr hC) hL).mpr
    have hU : (0 : ℝ) ≤ ((degree - S.degree a : ℕ) : ℝ) *
        ((degree - S.degree b : ℕ) : ℝ) := by positivity
    have hA : (0 : ℝ) ≤ Nat.card (PatternPresent (degree := degree) S a b) := by positivity
    nlinarith
  · have hzero : Nat.card (PatternClass (degree := degree) S) = 0 := by omega
    have hAzero : Nat.card (PatternPresent (degree := degree) S a b) = 0 := by omega
    rw [hzero, hAzero]
    simp only [Nat.cast_zero, zero_div]
    positivity

def patternPresentSubtypeEquiv (S : SimpleGraph (Fin N)) (a b : Fin N) :
    {g : PatternClass (degree := degree) S // g.val.graph.Adj a b} ≃
      PatternPresent (degree := degree) S a b where
  toFun g := ⟨g.val.val, g.val.property, g.property⟩
  invFun g := ⟨⟨g.val, g.property.1⟩, g.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The preceding cardinal bound is exactly the probability for the uniform
law conditioned on containing S. Nonempty conditioning makes this a normalized law. -/
theorem pattern_conditional_uniform_probability (S : SimpleGraph (Fin N)) (a b : Fin N)
    (hab : ¬S.Adj a b)
    (hpositive : 0 < N * degree - patternSwitchSlack degree (graphEdgeCount S)) :
    eventMass (finiteUniformWeight (PatternClass (degree := degree) S))
        (fun g => g.val.graph.Adj a b) ≤
      ((degree - S.degree a : ℕ) : ℝ) * ((degree - S.degree b : ℕ) : ℝ) /
        ((N * degree - patternSwitchSlack degree (graphEdgeCount S) : ℕ) : ℝ) := by
  rw [uniform_eventMass_cardinality,
    Nat.card_congr (patternPresentSubtypeEquiv (degree := degree) S a b),
    ← Nat.card_eq_fintype_card]
  exact pattern_conditional_card_probability S a b hab hpositive

/-- Unconditional uniform-regular-graph mass recurrence. Iterating this
retains the falling-degree factors as required edges are added. -/
theorem pattern_edge_eventMass_bound (S : SimpleGraph (Fin N)) (a b : Fin N)
    (hab : ¬S.Adj a b)
    (hpositive : 0 < N * degree - patternSwitchSlack degree (graphEdgeCount S)) :
    eventMass (weight (N := N) (d := degree))
        (fun g => S ≤ g.graph ∧ g.graph.Adj a b) ≤
      (((degree - S.degree a : ℕ) : ℝ) * ((degree - S.degree b : ℕ) : ℝ) /
        ((N * degree - patternSwitchSlack degree (graphEdgeCount S) : ℕ) : ℝ)) *
          eventMass (weight (N := N) (d := degree)) (fun g => S ≤ g.graph) := by
  have hcount := pattern_switching_count (degree := degree) S a b hab
  have hpartition := pattern_class_card_partition (degree := degree) S a b
  have hL : (0 : ℝ) < (N * degree - patternSwitchSlack degree (graphEdgeCount S) : ℕ) :=
    Nat.cast_pos.mpr hpositive
  have hcountR : (Nat.card (PatternPresent (degree := degree) S a b) : ℝ) *
      ((N * degree - patternSwitchSlack degree (graphEdgeCount S) : ℕ) : ℝ) ≤
        (Nat.card (PatternAbsent (degree := degree) S a b) : ℝ) *
          (((degree - S.degree a : ℕ) : ℝ) * ((degree - S.degree b : ℕ) : ℝ)) := by
    exact_mod_cast hcount
  have hpartitionR : (Nat.card (PatternClass (degree := degree) S) : ℝ) =
      (Nat.card (PatternPresent (degree := degree) S a b) : ℝ) +
        (Nat.card (PatternAbsent (degree := degree) S a b) : ℝ) := by exact_mod_cast hpartition
  have hU : (0 : ℝ) ≤ ((degree - S.degree a : ℕ) : ℝ) *
      ((degree - S.degree b : ℕ) : ℝ) := by positivity
  have hA : (0 : ℝ) ≤ Nat.card (PatternPresent (degree := degree) S a b) := by positivity
  have hcore : (Nat.card (PatternPresent (degree := degree) S a b) : ℝ) ≤
      ((((degree - S.degree a : ℕ) : ℝ) * ((degree - S.degree b : ℕ) : ℝ)) /
        ((N * degree - patternSwitchSlack degree (graphEdgeCount S) : ℕ) : ℝ)) *
          (Nat.card (PatternClass (degree := degree) S) : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hL).mpr
    nlinarith
  change eventMass (finiteUniformWeight (RegularGraph N degree)) _ ≤
    _ * eventMass (finiteUniformWeight (RegularGraph N degree)) _
  rw [uniform_eventMass_cardinality, uniform_eventMass_cardinality]
  have hmass := div_le_div_of_nonneg_right hcore
    (Nat.cast_nonneg (Fintype.card (RegularGraph N degree)) :
      (0 : ℝ) ≤ Fintype.card (RegularGraph N degree))
  simpa only [PatternPresent, PatternClass, mul_div_assoc] using hmass

/-- A uniform positive lower budget can replace the pattern-dependent
denominator. This is useful when all required patterns have at most a fixed
number of edges. -/
theorem pattern_edge_eventMass_bound_of_budget (S : SimpleGraph (Fin N)) (a b : Fin N)
    (hab : ¬S.Adj a b) (L : ℕ) (hL : 0 < L)
    (hbudget : L ≤ N * degree - patternSwitchSlack degree (graphEdgeCount S)) :
    eventMass (weight (N := N) (d := degree))
        (fun g => S ≤ g.graph ∧ g.graph.Adj a b) ≤
      (((degree - S.degree a : ℕ) : ℝ) * ((degree - S.degree b : ℕ) : ℝ) / (L : ℝ)) *
        eventMass (weight (N := N) (d := degree)) (fun g => S ≤ g.graph) := by
  have hpositive := lt_of_lt_of_le hL hbudget
  apply (pattern_edge_eventMass_bound S a b hab hpositive).trans
  apply mul_le_mul_of_nonneg_right
  · apply div_le_div_of_nonneg_left (by positivity) (Nat.cast_pos.mpr hL)
    exact_mod_cast hbudget
  · unfold eventMass
    apply Finset.sum_nonneg
    intro g _
    split_ifs
    · exact g.weight_nonnegative
    · exact le_rfl

/-- Adding a genuinely new required edge gives the same mass recurrence. -/
theorem pattern_extension_eventMass_bound (S : SimpleGraph (Fin N)) (a b : Fin N)
    (habDistinct : a ≠ b) (hab : ¬S.Adj a b) (L : ℕ) (hL : 0 < L)
    (hbudget : L ≤ N * degree - patternSwitchSlack degree (graphEdgeCount S)) :
    eventMass (weight (N := N) (d := degree))
        (fun g => S ⊔ SimpleGraph.edge a b ≤ g.graph) ≤
      (((degree - S.degree a : ℕ) : ℝ) * ((degree - S.degree b : ℕ) : ℝ) / (L : ℝ)) *
        eventMass (weight (N := N) (d := degree)) (fun g => S ≤ g.graph) := by
  have hevent : (fun g : RegularGraph N degree => S ⊔ SimpleGraph.edge a b ≤ g.graph) =
      (fun g => S ≤ g.graph ∧ g.graph.Adj a b) := by
    funext g
    exact propext (required_sup_edge_iff S g.graph a b habDistinct)
  rw [hevent]
  exact pattern_edge_eventMass_bound_of_budget S a b hab L hL hbudget

end RegularGraph

end LocalLaw
