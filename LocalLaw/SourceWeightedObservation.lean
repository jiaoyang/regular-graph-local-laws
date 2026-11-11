import LocalLaw.SourceObservationConcentration
import LocalLaw.ActualWeightedConcentration

/-!
# Source concentration for the actual Green-product weights

The observation bound, true mean, sampling independence, inverse-power tail,
weight norms and numerical feedback are all derived. The finite model's
actual component reference budget and diameter remain geometric inputs.
-/

open Filter
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceWeightedObservationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_boundaryProductWeight_concentration (a b d q : ℕ) (c β γ B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hγ : c / 4 < γ) (hgap : γ + β < 1)
    (hB : 0 ≤ B) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∀ Cq badCount : ℕ, badCount ≤ ⌊(N : ℝ) ^ γ⌋₊ →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ (S : Set (Fin N)) (hS : graphBallVertices g.graph o (actualCavityDepth a d N z - 1) ⊆ S),
      (g.deficient.restrict S).ComponentFiniteReferenceBudget →
      (∀ i j : S, (g.deficient.restrict S).graph.dist i j ≤
        singletonObservationDiameter d (effectiveModelRadius a d N β)) →
      let L := Real.log (N : ℝ)
      let ell := actualCavityDepth a d N z - 1
      let r := effectiveModelRadius a d N β
      let R := logarithmicRadius (c / 4) d N
      let A := sourceObservationLogCap d β
      let amplitude := DeficientGraph.singletonObservationConstant d * C1 *
        g.sourcePrime a (logarithmicRadius β d N) z
      let δ := 3 * graphPaperError a d N (logarithmicRadius β d N) z / L ^ 16
      eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o ell))
        (fun samples => ∃ i : S,
          (32 * (d : ℝ) * finiteExtraReferenceConstant d ^ 4 * A + 1) * L ^ 2 * amplitude /
              resamplingDecayDenominator d ell +
            δ * (8 * (d : ℝ) * finiteExtraReferenceConstant d ^ 2 * A) * L <
          ‖∑ α, g.deficient.boundaryProductWeight S o ell hS (g.Q z) z i α *
            (g.sourceSingletonObservation (graphBallVertices g.graph o ell) r (R / 4) z (g.Q z) (samples α) -
              (g.Q z - cavityIterate z (g.Q z) (r + 1)))‖) ≤ 1 / (N : ℝ) ^ q := by
  filter_upwards [eventually_sourceSingletonObservation_concentration a b d q c β γ B C1
    ha hb hd hc hβ hβc hγ hgap hB hC1,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1]
    with N hconcentration hparameters
  intro g o z hz hzB hscale Cq badCount hbad hplus S hS hbudget hdiam
  dsimp only
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let ell := actualCavityDepth a d N z - 1
  let r := effectiveModelRadius a d N β
  let R := logarithmicRadius (c / 4) d N
  let A := sourceObservationLogCap d β
  let amplitude := DeficientGraph.singletonObservationConstant d * C1 * g.sourcePrime a (logarithmicRadius β d N) z
  let δ := 3 * ε / L ^ 16
  let w : S → BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell) → ℂ :=
    g.deficient.boundaryProductWeight S o ell hS (g.Q z) z
  have parameters := hparameters z hz hscale
  have hL : 1 ≤ L := parameters.log_one
  have hA : 0 ≤ A := parameters.log_cap_nonnegative
  have hε : 0 ≤ ε := parameters.error_nonnegative
  have hC10 : 0 ≤ C1 := (by norm_num : (0 : ℝ) ≤ 1).trans hC1
  have hprior : ‖g.Q z - semicircleRoot z‖ ≤ C1 * scalarScale (spectralScale z) ε := hplus.cavity
  have hpriorScaled := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) hε hC1)
  have hscaled : 0 ≤ C1 ^ 2 * ε := mul_nonneg (sq_nonneg C1) hε
  obtain ⟨smallG, _, _, _, _⟩ := DeficientGraph.weak_localization_feedback_budgets d hd z (g.Q z) hz B
    (C1 ^ 2 * ε) L A hscaled hL hA parameters.error_scaled hpriorScaled
      (singletonObservationDiameter d r) (4 * r + 1) parameters.diameter_log parameters.pair_log parameters.localization_large
  have hcard : Fintype.card S ≤ N := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le S
  have hfamily := hconcentration g o z hz hzB hscale Cq badCount hbad hplus S hcard w
  have hprime : 0 ≤ g.sourcePrime a (logarithmicRadius β d N) z := by
    change 0 ≤ L ^ 3 * ε
    positivity
  have hamp : 0 ≤ amplitude := by
    have hconst : 0 ≤ DeficientGraph.singletonObservationConstant d := by
      unfold DeficientGraph.singletonObservationConstant
      positivity
    exact mul_nonneg (mul_nonneg hconst hC10) hprime
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  apply (eventMass_mono _ finiteUniformWeight_nonneg ?_).trans hfamily
  intro samples hfailure
  obtain ⟨i, hi⟩ := hfailure
  refine ⟨i, ?_⟩
  obtain ⟨hl1, hl2, _⟩ := g.deficient.boundaryProductWeight_log_bounds hd S hbudget o ell hS
    (g.Q z) z hz (g.Q_im_nonnegative z hz) (singletonObservationDiameter d r) hdiam smallG
      A L hA hL parameters.diameter_log i
  have hnoise := mul_le_mul_of_nonneg_left hl2
    (mul_nonneg (by linarith : 0 ≤ L) hamp)
  have hbias := mul_le_mul_of_nonneg_left hl1 hδ
  have hthreshold : L * amplitude * Real.sqrt (∑ α, ‖w i α‖ ^ 2) + δ * (∑ α, ‖w i α‖) ≤
      (32 * (d : ℝ) * finiteExtraReferenceConstant d ^ 4 * A + 1) * L ^ 2 * amplitude /
          resamplingDecayDenominator d ell +
        δ * (8 * (d : ℝ) * finiteExtraReferenceConstant d ^ 2 * A) * L := by
    convert add_le_add hnoise hbias using 1
    ring
  exact lt_of_le_of_lt hthreshold hi

end RegularGraph
end LocalLaw
