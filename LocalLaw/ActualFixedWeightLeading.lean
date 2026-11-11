import LocalLaw.SourceFixedWeightConcentration
import LocalLaw.ActualGoodDiagonalObservation
import LocalLaw.StrongWeightedDiagonalParameters
import LocalLaw.WeightedGoodDiagonal

/-!
# Actual good diagonal forcing for any deterministic finite weight family

This interface includes the neighbor-deleted cavity weights. Its scalar
observation bound, true mean and physical good-label error are derived from
the actual source events. Weight profiles are deterministic geometric data;
the named concentration event has a genuine polynomial tail in the companion
module.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance actualFixedWeightLeadingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def actualFixedWeightLeadingConstant (d : ℕ) (C1 Cnoise A1 Kbad W : ℝ) : ℝ :=
  let Cobs := DeficientGraph.singletonObservationConstant d * C1
  Cnoise * Cobs + 4 * A1 + (2 * Cobs + 3) * Kbad * W

namespace RegularGraph

theorem eventually_actual_fixed_weight_leading (a b d : ℕ) (c β γ B C1 Cnoise A1 Kbad W : ℝ) (Cq : ℕ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hγ : c / 4 < γ) (hgap : γ + β < 1)
    (hB : 0 ≤ B) (hC1 : 1 ≤ C1) (hnoise : 0 ≤ Cnoise) (hA1 : 0 ≤ A1)
    (hbad : 0 ≤ Kbad) (hW : 0 ≤ W)
    (hCdel : sourceDeletionConstant d β B ≤ C1) (hCq : finiteOmega d ≤ Cq) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∀ badCount : ℕ, badCount ≤ ⌊(N : ℝ) ^ γ⌋₊ →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ (J : Type) [Fintype J]
      (w : J → BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)) → ℂ),
      (∀ j, ∑ α, ‖w j α‖ ≤ A1 * Real.log (N : ℝ)) →
      (∀ j α, ‖w j α‖ ≤ W / resamplingDecayDenominator d (actualCavityDepth a d N z - 1)) →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      let selector := logarithmicRadius (c / 4) d N / 4
      let s := g.admissibleState T labels samples
      let gnew := g.labelledResampledGraph T labels samples selector
      let L := Real.log (N : ℝ)
      let ε := graphPaperError a d N (logarithmicRadius β d N) z
      let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
      ∀ targetBadCount : ℕ,
      gnew.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (finiteOmega d) targetBadCount z →
      ∀ good : Finset ι,
      (∀ i ∈ good, s.Eligible selector i) →
      (∀ i ∈ good, labels i ∈ g.sourceCorrelationGoodLabels T z φ selector samples) →
      ((Finset.univ \ good).card : ℝ) ≤ Kbad * L ^ 2 →
      g.SourceFixedWeightGood a c β C1 Cnoise A1 o z w samples →
      ∀ j : J,
      ‖∑ i ∈ good, w j (labels i) *
        ((gnew.deficient.delete T).G z (s.sampledOutsideSecond i).val (s.sampledOutsideSecond i).val - g.Q z)‖ ≤
        actualFixedWeightLeadingConstant d C1 Cnoise A1 Kbad W * (ε / L ^ 4) := by
  let Cobs := DeficientGraph.singletonObservationConstant d * C1
  have hC10 : 0 ≤ C1 := (by norm_num : (0 : ℝ) ≤ 1).trans hC1
  have hobs : 0 ≤ Cobs := by dsimp only [Cobs, DeficientGraph.singletonObservationConstant]; positivity
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
  intro g o z hz hzB hfloor badCount hbadCount hplus J _ w hl1 hmax ι _ labels samples
  dsimp only
  let L := Real.log (N : ℝ)
  let ell := actualCavityDepth a d N z - 1
  let r := effectiveModelRadius a d N β
  let selector := logarithmicRadius (c / 4) d N / 4
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T labels samples
  let gnew := g.labelledResampledGraph T labels samples selector
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let D := resamplingDecayDenominator d ell
  let amp := Cobs * g.sourcePrime a (logarithmicRadius β d N) z
  let bias := 3 * ε / L ^ 16
  let error := ε / L ^ 16
  let Y := cavityIterate z (g.Q z) (r + 1)
  let Z := g.sourceSingletonObservation T r selector z (g.Q z)
  let V := fun i => (gnew.deficient.delete T).G z (s.sampledOutsideSecond i).val (s.sampledOutsideSecond i).val
  intro targetBadCount target good heligible hcorrelation hbadCard hconcentration j
  have num := hnum z hz hfloor
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
  have hZcap : ∀ e, ‖Z e‖ ≤ amp := hZ g o z hz hfloor hzB Cq badCount hplus
  have hZmean : ‖finiteComplexMean Z - (g.Q z - Y)‖ ≤ bias :=
    hmean g o z hz hzB hfloor Cq badCount hbadCount hplus
  have hcenter : ∀ i ∉ good, ‖Z (samples (labels i)) - (g.Q z - Y)‖ ≤ 2 * amp + bias := by
    intro i _
    exact observation_centered_bound_of_mean_bias Z (g.Q z - Y) amp bias hZcap hZmean _
  have hgood : ∀ i ∈ good, ‖V i - Y - Z (samples (labels i))‖ ≤ error := by
    intro i hi
    exact hdiagonal g o z hz hzB hfloor badCount hplus labels samples targetBadCount target
      ⟨i, heligible i hi⟩ (hcorrelation i hi)
  let wl := fun i => w j (labels i)
  have hweight : ∀ i ∉ good, ‖wl i‖ ≤ W / D := fun i _ => hmax j (labels i)
  have hl1label : (∑ i, ‖wl i‖) ≤ A1 * L := by
    rw [show (∑ i, ‖wl i‖) = ∑ α, ‖w j α‖ by
      simpa only [wl] using labels.sum_comp (fun α => ‖w j α‖)]
    exact hl1 j
  have htransfer := weighted_good_diagonal_card_transfer good wl V (fun i => Z (samples (labels i)))
    Y (g.Q z) error (2 * amp + bias) (W / D) herror (by positivity) (by positivity)
      hgood hcenter hweight
  have hsum : (∑ i, wl i * (Z (samples (labels i)) - (g.Q z - Y))) =
      ∑ α, w j α * (Z (samples α) - (g.Q z - Y)) := by
    simpa only [wl] using labels.sum_comp (fun α => w j α * (Z (samples α) - (g.Q z - Y)))
  rw [hsum] at htransfer
  have hconc := hconcentration j
  have herr := mul_le_mul_of_nonneg_left hl1label herror
  have hbadCost := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbadCard
    (show 0 ≤ 2 * amp + bias by positivity)) (show 0 ≤ W / D by positivity)
  have htotal := htransfer.trans (add_le_add (add_le_add hconc herr) hbadCost)
  apply htotal.trans
  convert hnumeric (logarithmicRadius β d N) z hz.le using 1
  dsimp only [error, amp, bias, sourcePrime, inflatedPrime, actualFixedWeightLeadingConstant, Cobs]
  ring

end RegularGraph
end LocalLaw
