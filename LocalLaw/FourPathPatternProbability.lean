import LocalLaw.FourPathActualEmbedding
import LocalLaw.FinitePatternFamilyProbability
import LocalLaw.BicyclicProbabilityParameters

/-!
# Probability of an actual bicyclic ball witness

Valid canonical four-tail parameters are connected excess-two patterns with
at most eight vertices of degree different from two. Their actual parameter
count and switching probabilities give the sharp logarithmic-radius bound.
Together with the checked bad-center first moment, this proves the original
structural event has mass at least one half on each nonempty regular ensemble.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000

namespace LocalLaw

local instance fourPathProbabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def ValidFourPathParameters (R : ℕ) :=
  {P : FourPathParameters R // graphExcess (fourPathBicyclicGraph P) = 2}

instance validFourPathParametersFintype (R : ℕ) : Fintype (ValidFourPathParameters R) := by
  unfold ValidFourPathParameters
  infer_instance

theorem validFourPathParameters_card_bound (R : ℕ) :
    Nat.card (ValidFourPathParameters R) ≤ (R + 1) ^ 4 * (4 * R + 2) ^ 3 :=
  (Nat.card_le_card_of_injective (fun P : ValidFourPathParameters R => P.val)
    Subtype.val_injective).trans (fourPathParameters_card_bound R)

theorem fourPath_pattern_vertex_bound {R : ℕ} (P : FourPathParameters R) :
    fourStageSize P.1 4 ≤ 4 * R + 1 := by
  have h := fourStageSize_bound P.1 4
  omega

theorem validFourPath_pattern_edge_bound {R : ℕ} (P : ValidFourPathParameters R) :
    graphEdgeCount (fourPathBicyclicGraph P.val) ≤ 4 * R + 2 := by
  have hEuler := connected_graph_excess_euler (fourPathBicyclicGraph P.val)
    (fourPathBicyclicGraph_connected P.val)
  rw [P.property] at hEuler
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hEuler
  have hn := fourPath_pattern_vertex_bound P.val
  omega

namespace RegularGraph

variable {N d : ℕ}

/-- Finite probability bound for the actual valid canonical pattern family. -/
theorem fourPath_pattern_family_mass_bound (R : ℕ) (hN : 0 < N) (hd : 2 ≤ d)
    (hbudget : 2 * (4 * R + 2) * patternSwitchSlack d (4 * R + 2) ≤ N * d) :
    eventMass (weight (N := N) (d := d)) (fun g =>
      ∃ P : FourPathParameters R, graphExcess (fourPathBicyclicGraph P) = 2 ∧
        ∃ f : Fin (fourStageSize P.1 4) ↪ Fin N, (fourPathBicyclicGraph P).map f ≤ g.graph) ≤
      (((R + 1) ^ 4 * (4 * R + 2) ^ 3 : ℕ) : ℝ) *
        (2 * (((d ^ d : ℕ) : ℝ) ^ 8) * (((d - 1 : ℕ) : ℝ) ^ (4 * R + 1)) / (N : ℝ)) := by
  have hdegree : ∀ P : ValidFourPathParameters R, ∀ v,
      v ∉ fourTrieSpecial P.val 4 le_rfl → (fourPathBicyclicGraph P.val).degree v = 2 := by
    intro P v hv
    have h := fourPathBicyclicGraph_degree_two_off P.val v hv
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using h
  have hfamily := finite_bicyclic_pattern_family_bound
    (fun P : ValidFourPathParameters R => fourStageSize P.val.1 4)
    (fun P => fourPathBicyclicGraph P.val) 8 (4 * R + 1) (4 * R + 2)
    (fun P => fourTrieSpecial P.val 4 le_rfl)
    (fun P => fourPathBicyclicGraph_connected P.val) (fun P => P.property)
    (fun P => fourTrieSpecial_card_four P.val) hdegree
    (fun P => fourPath_pattern_vertex_bound P.val)
    (fun P => validFourPath_pattern_edge_bound P) hN hd hbudget
  have hcover : ∀ g : RegularGraph N d,
      (∃ P : FourPathParameters R, graphExcess (fourPathBicyclicGraph P) = 2 ∧
        ∃ f : Fin (fourStageSize P.1 4) ↪ Fin N, (fourPathBicyclicGraph P).map f ≤ g.graph) →
      ∃ P : ValidFourPathParameters R, ∃ f : Fin (fourStageSize P.val.1 4) ↪ Fin N,
        (fourPathBicyclicGraph P.val).map f ≤ g.graph := by
    rintro g ⟨P, hP, f, hf⟩
    exact ⟨⟨P, hP⟩, f, hf⟩
  apply ((eventMass_mono weight weight_nonnegative hcover).trans hfamily).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast (show Fintype.card (ValidFourPathParameters R) ≤
      (R + 1) ^ 4 * (4 * R + 2) ^ 3 by
    simpa only [Nat.card_eq_fintype_card] using validFourPathParameters_card_bound R)

/-- Every actual excess-two-or-more ball supplies one of the counted patterns. -/
theorem ball_excess_two_mass_bound (R : ℕ) (hN : 0 < N) (hd : 2 ≤ d)
    (hbudget : 2 * (4 * R + 2) * patternSwitchSlack d (4 * R + 2) ≤ N * d) :
    eventMass (weight (N := N) (d := d)) (fun g => ∃ o, 2 ≤ graphBallExcess g.graph o R) ≤
      (((R + 1) ^ 4 * (4 * R + 2) ^ 3 : ℕ) : ℝ) *
        (2 * (((d ^ d : ℕ) : ℝ) ^ 8) * (((d - 1 : ℕ) : ℝ) ^ (4 * R + 1)) / (N : ℝ)) := by
  apply (eventMass_mono weight weight_nonnegative ?_).trans
    (fourPath_pattern_family_mass_bound R hN hd hbudget)
  rintro g ⟨o, ho⟩
  exact ball_four_path_bicyclic_pattern g.graph o R ho

end RegularGraph

/-- At the actual structural radius, bicyclic balls have vanishing probability
for every c<1. No expected witness count is an input. -/
theorem eventually_ball_excess_two_tail_small (d : ℕ) (c δ : ℝ) (hd : 3 ≤ d)
    (hc : 0 ≤ c) (hc₁ : c < 1) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        ∃ o, 2 ≤ graphBallExcess g.graph o (logarithmicRadius (c / 4) d N)) ≤ δ := by
  filter_upwards [eventually_bicyclic_family_budget d c δ hd hc hc₁ hδ] with N hnum
  exact (RegularGraph.ball_excess_two_mass_bound _ hnum.1 (by omega) hnum.2.1).trans hnum.2.2

/-- All structural-radius balls have excess at most one with mass at least
1-delta, on every nonempty actual regular-graph ensemble. -/
theorem eventually_ball_excess_good_mass (d : ℕ) (c δ : ℝ) (hd : 3 ≤ d)
    (hc : 0 ≤ c) (hc₁ : c < 1) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in Filter.atTop, Nonempty (RegularGraph N d) →
      1 - δ ≤ eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        ∀ o, graphBallExcess g.graph o (logarithmicRadius (c / 4) d N) ≤ 1) := by
  filter_upwards [eventually_ball_excess_two_tail_small d c δ hd hc hc₁ hδ] with N htail
  intro hnonempty
  letI : Nonempty (RegularGraph N d) := hnonempty
  let P : RegularGraph N d → Prop := fun g =>
    ∀ o, graphBallExcess g.graph o (logarithmicRadius (c / 4) d N) ≤ 1
  have hcompl : eventMass RegularGraph.weight (fun g => ¬P g) ≤ δ := by
    simpa only [P, not_forall, not_le] using htail
  have hsum := finiteUniform_eventMass_complement_sum P
  change eventMass RegularGraph.weight P + eventMass RegularGraph.weight (fun g => ¬P g) = 1 at hsum
  linarith

/-- The original source structural event has actual uniform mass at least
one half, rather than assuming its conditioning denominator is large. -/
theorem eventually_original_structural_mass_half (d ω : ℕ) (c : ℝ)
    (hd : 3 ≤ d) (hω : 1 ≤ ω) (hc : 0 < c) (hc₁ : c < 1) :
    ∀ᶠ N : ℕ in Filter.atTop, Nonempty (RegularGraph N d) →
      1 / 2 ≤ eventMass (RegularGraph.weight (N := N) (d := d))
        (RegularGraph.structural (logarithmicRadius (c / 4) d N) ω ⌊(N : ℝ) ^ c⌋₊) := by
  have hball := eventually_ball_excess_two_tail_small d c (1 / 4) hd hc.le hc₁ (by norm_num)
  have hbad := eventually_badCenter_tail_small d c c (1 / 4) hd hc.le (by linarith) (by norm_num)
  filter_upwards [hball, hbad] with N hball hbad
  intro hnonempty
  letI : Nonempty (RegularGraph N d) := hnonempty
  let R := logarithmicRadius (c / 4) d N
  let P : RegularGraph N d → Prop := RegularGraph.structural R ω ⌊(N : ℝ) ^ c⌋₊
  have hcover : ∀ g : RegularGraph N d, ¬P g →
      (∃ o, 2 ≤ graphBallExcess g.graph o R) ∨
        (N : ℝ) ^ c < ((nonTreeCenters g.graph R).card : ℝ) := by
    intro g hnot
    by_cases hex : ∃ o, 2 ≤ graphBallExcess g.graph o R
    · exact Or.inl hex
    · right
      by_contra hnone
      have hle : ((nonTreeCenters g.graph R).card : ℝ) ≤ (N : ℝ) ^ c := le_of_not_gt hnone
      have hcount : (nonTreeCenters g.graph R).card ≤ ⌊(N : ℝ) ^ c⌋₊ :=
        (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) c)).mpr hle
      have hexcess : ∀ o, graphBallExcess g.graph o R ≤ ω := by
        intro o
        have hh : ¬2 ≤ graphBallExcess g.graph o R := fun h => hex ⟨o, h⟩
        have hsmall : graphBallExcess g.graph o R ≤ 1 := by omega
        exact hsmall.trans hω
      exact hnot ⟨hexcess, hcount⟩
  have hfailure : eventMass RegularGraph.weight (fun g => ¬P g) ≤ 1 / 2 := by
    have h := (eventMass_mono RegularGraph.weight RegularGraph.weight_nonnegative hcover).trans
      (eventMass_union_le RegularGraph.weight RegularGraph.weight_nonnegative _ _)
    have h' := h.trans (add_le_add hball hbad)
    norm_num at h' ⊢
    exact h'
  have hsum := finiteUniform_eventMass_complement_sum P
  change eventMass RegularGraph.weight P + eventMass RegularGraph.weight (fun g => ¬P g) = 1 at hsum
  linarith

end LocalLaw
