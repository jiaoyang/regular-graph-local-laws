import LocalLaw.ActualLeadingDiagonal
import LocalLaw.StrongWeightedDiagonalParameters

/-! # Actual good diagonal forcing at its fourth-log rate -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance actualLeadingDiagonalStrongDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def actualLeadingDiagonalStrongConstant (d : ℕ) (β C1 Kbad : ℝ) : ℝ :=
  let A := sourceObservationLogCap d β
  let Cnoise := 32 * (d : ℝ) * finiteExtraReferenceConstant d ^ 4 * A + 1
  let Cobs := DeficientGraph.singletonObservationConstant d * C1
  let A1 := 8 * (d : ℝ) * finiteExtraReferenceConstant d ^ 2 * A
  let W := 4 * finiteExtraReferenceConstant d ^ 2
  Cnoise * Cobs + 4 * A1 + (2 * Cobs + 3) * Kbad * W

namespace RegularGraph

theorem eventually_actual_leading_diagonal_strong (a b d : ℕ) (c β γ B C1 Kbad : ℝ) (Cq : ℕ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hγ : c / 4 < γ) (hgap : γ + β < 1)
    (hB : 0 ≤ B) (hC1 : 1 ≤ C1) (hbad : 0 ≤ Kbad)
    (hCdel : sourceDeletionConstant d β B ≤ C1) (hCq : finiteOmega d ≤ Cq) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∀ badCount : ℕ, badCount ≤ ⌊(N : ℝ) ^ γ⌋₊ →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ (S : Set (Fin N)) (hS : graphBallVertices g.graph o (actualCavityDepth a d N z - 1) ⊆ S),
      (g.deficient.restrict S).ComponentFiniteReferenceBudget →
      (∀ x y : S, (g.deficient.restrict S).graph.dist x y ≤
        singletonObservationDiameter d (effectiveModelRadius a d N β)) →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      let selector := logarithmicRadius (c / 4) d N / 4
      let s := g.admissibleState T boundary samples
      let gnew := g.labelledResampledGraph T boundary samples selector
      let φ := correlationThreshold (Real.log (N : ℝ)) a N z.im (graphKestenMcKayReference d z).im
        (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z)
      ∀ targetBadCount : ℕ,
      gnew.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (finiteOmega d) targetBadCount z →
      ∀ good : Finset ι,
      (∀ j ∈ good, s.Eligible selector j) →
      (∀ j ∈ good, boundary j ∈ g.sourceCorrelationGoodLabels T z φ selector samples) →
      ((Finset.univ \ good).card : ℝ) ≤ Kbad * Real.log (N : ℝ) ^ 2 →
      g.SourceWeightedObservationGood a c β C1 o z S hS samples →
      ∀ i : S,
      ‖∑ j ∈ good, g.deficient.boundaryProductWeight S o (actualCavityDepth a d N z - 1)
          hS (g.Q z) z i (boundary j) *
        ((gnew.deficient.delete T).G z (s.sampledOutsideSecond j).val (s.sampledOutsideSecond j).val - g.Q z)‖ ≤
          actualLeadingDiagonalStrongConstant d β C1 Kbad *
            (graphPaperError a d N (logarithmicRadius β d N) z / Real.log (N : ℝ) ^ 4) := by
  let A := sourceObservationLogCap d β
  let Cnoise := 32 * (d : ℝ) * finiteExtraReferenceConstant d ^ 4 * A + 1
  let Cobs := DeficientGraph.singletonObservationConstant d * C1
  let A1 := 8 * (d : ℝ) * finiteExtraReferenceConstant d ^ 2 * A
  let W := 4 * finiteExtraReferenceConstant d ^ 2
  have hA : 0 ≤ A := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hC10 : 0 ≤ C1 := (by norm_num : (0 : ℝ) ≤ 1).trans hC1
  have hnoise : 0 ≤ Cnoise := by dsimp only [Cnoise]; positivity
  have hobs : 0 ≤ Cobs := by dsimp only [Cobs, DeficientGraph.singletonObservationConstant]; positivity
  have hA1 : 0 ≤ A1 := by dsimp only [A1]; positivity
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_actual_good_diagonal_observation a b d c β B C1 Cq
    ha hb hd hc hβ hβc hB hC1 hCdel hCq,
    eventually_sourceSingletonObservation_bound a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceSingletonObservation_mean_bias a b d c β γ B C1 ha hb hd hc hβ hβc hγ hgap hB hC1,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_good_weighted_diagonal_strong_budget a d Cnoise Cobs A1 Kbad W
      ha hd hnoise hobs hA1 hbad hW,
    eventually_resampling_ball_budget a d hd, hdepth, Filter.eventually_ge_atTop 1]
    with N hdiagonal hZ hmean hnum hnumeric hball hdepth hN
  intro g o z hz hzB hscale badCount hbadCount hplus S hS hbudget hdiam ι _ boundary samples
  dsimp only
  let L := Real.log (N : ℝ)
  let ell := actualCavityDepth a d N z - 1
  let r := effectiveModelRadius a d N β
  let selector := logarithmicRadius (c / 4) d N / 4
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  let gnew := g.labelledResampledGraph T boundary samples selector
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let D := resamplingDecayDenominator d ell
  let amp := Cobs * g.sourcePrime a (logarithmicRadius β d N) z
  let bias := 3 * ε / L ^ 16
  let error := ε / L ^ 16
  let Y := cavityIterate z (g.Q z) (r + 1)
  let Z := g.sourceSingletonObservation T r selector z (g.Q z)
  let V := fun j => (gnew.deficient.delete T).G z (s.sampledOutsideSecond j).val (s.sampledOutsideSecond j).val
  intro targetBadCount target good heligible hcorrelation hbadCard hconcentration i
  have num := hnum z hz hscale
  have hε : 0 ≤ ε := num.error_nonnegative
  have hL : 1 ≤ L := num.log_one
  have hD : 0 < D := resamplingDecayDenominator_pos d ell hd
  have hprime : 0 ≤ g.sourcePrime a (logarithmicRadius β d N) z := by
    change 0 ≤ L ^ 3 * ε
    positivity
  have hamp : 0 ≤ amp := mul_nonneg hobs hprime
  have hbias : 0 ≤ bias := by dsimp only [bias]; positivity
  have herror : 0 ≤ error := by dsimp only [error]; positivity
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hT : 4 * Nat.card T ≤ N := by
    apply (Nat.mul_le_mul_left 4 ((g.ball_card_bound o ell).trans
      (Nat.pow_le_pow_right (by omega : 0 < d + 1) hell))).trans hball
  letI : Nonempty (OutsideOrientedEdge g.graph T) := g.outside_edge_nonempty T (by omega) (by omega) hT
  have hZcap : ∀ e, ‖Z e‖ ≤ amp := hZ g o z hz hscale hzB Cq badCount hplus
  have hZmean : ‖finiteComplexMean Z - (g.Q z - Y)‖ ≤ bias :=
    hmean g o z hz hzB hscale Cq badCount hbadCount hplus
  have hcenter : ∀ j ∉ good, ‖Z (samples (boundary j)) - (g.Q z - Y)‖ ≤ 2 * amp + bias := by
    intro j _
    exact observation_centered_bound_of_mean_bias Z (g.Q z - Y) amp bias hZcap hZmean _
  have hgood : ∀ j ∈ good, ‖V j - Y - Z (samples (boundary j))‖ ≤ error := by
    intro j hj
    exact hdiagonal g o z hz hzB hscale badCount hplus boundary samples targetBadCount target
      ⟨j, heligible j hj⟩ (hcorrelation j hj)
  have hprior := hplus.cavity.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) hε hC1)
  have hfeedback := (DeficientGraph.weak_localization_feedback_budgets d hd z (g.Q z) hz B
    (C1 ^ 2 * ε) L A (mul_nonneg (sq_nonneg C1) hε) hL hA num.error_scaled hprior
      (singletonObservationDiameter d r) (4 * r + 1) num.diameter_log num.pair_log num.localization_large).1
  obtain ⟨hl1, _, hmax⟩ := g.deficient.boundaryProductWeight_log_bounds hd S hbudget o ell hS
    (g.Q z) z hz (g.Q_im_nonnegative z hz) (singletonObservationDiameter d r) hdiam hfeedback A L hA hL num.diameter_log i
  let w := fun j => g.deficient.boundaryProductWeight S o ell hS (g.Q z) z i (boundary j)
  have hweight : ∀ j ∉ good, ‖w j‖ ≤ W / D := fun j _ => hmax (boundary j)
  have hl1label : (∑ j, ‖w j‖) ≤ A1 * L := by
    rw [show (∑ j, ‖w j‖) = ∑ α, ‖g.deficient.boundaryProductWeight S o ell hS (g.Q z) z i α‖ by
      simpa only [w] using boundary.sum_comp (fun α => ‖g.deficient.boundaryProductWeight S o ell hS (g.Q z) z i α‖)]
    exact hl1
  have htransfer := weighted_good_diagonal_card_transfer good w V (fun j => Z (samples (boundary j)))
    Y (g.Q z) error (2 * amp + bias) (W / D) herror (by positivity) (by positivity)
      hgood hcenter hweight
  have hsum : (∑ j, w j * (Z (samples (boundary j)) - (g.Q z - Y))) =
      ∑ α, g.deficient.boundaryProductWeight S o ell hS (g.Q z) z i α *
        (Z (samples α) - (g.Q z - Y)) := by
    simpa only [w] using boundary.sum_comp (fun α => g.deficient.boundaryProductWeight S o ell hS
      (g.Q z) z i α * (Z (samples α) - (g.Q z - Y)))
  rw [hsum] at htransfer
  have hconc := hconcentration i
  have herr := mul_le_mul_of_nonneg_left hl1label herror
  have hbadCost := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbadCard
    (show 0 ≤ 2 * amp + bias by positivity)) (show 0 ≤ W / D by positivity)
  have htotal := htransfer.trans (add_le_add (add_le_add hconc herr) hbadCost)
  apply htotal.trans
  convert hnumeric (logarithmicRadius β d N) z hz.le using 1
  dsimp only [error, amp, bias, sourcePrime, inflatedPrime]
  ring

end RegularGraph
end LocalLaw
