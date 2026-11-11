import LocalLaw.CyclePackingMomentBridge
import LocalLaw.StrongBadCenterParameters
import LocalLaw.SparseParameterAbsorption

/-!
# Arbitrary polynomial tails for the actual strengthened bad-center event

The finite packing proof and actual logarithmic parameters are combined.
Within the bounded-ball-excess event, the exceptional count N^gamma has every
polynomial failure bound whenever gamma>3c/4. In particular gamma=7c/8
permits all printed localization exponents beta<=c/32.
-/

namespace LocalLaw

/-- A genuine graph-probability result: all moments and all N-dependent
budgets have been supplied by the preceding concrete counting proofs. -/
theorem eventually_strong_badCenter_probability (d ω p : ℕ) (c γ : ℝ)
    (hd : 3 ≤ d) (hc : 0 ≤ c) (hγ : 3 * c / 4 < γ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        (∀ v, graphBallExcess g.graph v (logarithmicRadius (c / 4) d N) ≤ ω) ∧
          (N : ℝ) ^ γ < ((nonTreeCenters g.graph (logarithmicRadius (c / 4) d N)).card : ℝ)) ≤
        1 / (N : ℝ) ^ p := by
  filter_upwards [eventually_strong_badCenter_budgets d ω p c γ hd hc hγ] with N hN
  dsimp only at hN
  obtain ⟨hn, hq, hbudget, hthreshold, htail⟩ := hN
  let R := logarithmicRadius (c / 4) d N
  let q := sufficientMomentOrder (γ - 3 * c / 4) p
  let K := q * (2 * R + 1)
  have hgraph := RegularGraph.strong_badCenters_tail_bound R ω q K hd hq le_rfl hn
    hbudget ((N : ℝ) ^ γ) (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) γ) hthreshold
  exact hgraph.trans htail

/-- Passing from the original structural count to the stronger count costs
only an arbitrarily small polynomial error under the original graph law. -/
theorem eventually_strengthened_structural_difference (d ω p : ℕ) (c γ : ℝ)
    (hd : 3 ≤ d) (hc : 0 ≤ c) (hγ : 3 * c / 4 < γ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ badCount : ℕ,
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        RegularGraph.structural (logarithmicRadius (c / 4) d N) ω badCount g ∧
          ¬ RegularGraph.structural (logarithmicRadius (c / 4) d N) ω
            ⌊(N : ℝ) ^ γ⌋₊ g) ≤ 1 / (N : ℝ) ^ p := by
  classical
  filter_upwards [eventually_strong_badCenter_probability d ω p c γ hd hc hγ] with N htail
  intro badCount
  apply (eventMass_mono RegularGraph.weight RegularGraph.weight_nonnegative ?_).trans htail
  intro g hg
  change GraphTreeLike g.graph _ ω badCount ∧ ¬ GraphTreeLike g.graph _ ω _ at hg
  refine ⟨hg.1.1, ?_⟩
  by_contra hnot
  have hle : ((nonTreeCenters g.graph (logarithmicRadius (c / 4) d N)).card : ℝ) ≤ (N : ℝ) ^ γ :=
    le_of_not_gt hnot
  have hfloor : (nonTreeCenters g.graph (logarithmicRadius (c / 4) d N)).card ≤ ⌊(N : ℝ) ^ γ⌋₊ :=
    (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr hle
  exact hg.2 ⟨hg.1.1, hfloor⟩

/-- The strengthened count exponent is available for every positive c. -/
theorem eventually_sevenEighths_structural_difference (d ω p : ℕ) (c : ℝ)
    (hd : 3 ≤ d) (hc : 0 < c) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ badCount : ℕ,
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        RegularGraph.structural (logarithmicRadius (c / 4) d N) ω badCount g ∧
          ¬ RegularGraph.structural (logarithmicRadius (c / 4) d N) ω
            ⌊(N : ℝ) ^ (7 * c / 8)⌋₊ g) ≤ 1 / (N : ℝ) ^ p :=
  eventually_strengthened_structural_difference d ω p c (7 * c / 8) hd hc.le (by linarith)

/-- The explicit source correction simultaneously supports every printed
localization exponent, once the stronger good event is used. -/
theorem sevenEighths_sparse_compatible (c β : ℝ) (hc : c < 1) (hβ : β ≤ c / 32) :
    7 * c / 8 + β ≤ 1 := strengthened_sparse_exponent c β hc hβ

end LocalLaw
