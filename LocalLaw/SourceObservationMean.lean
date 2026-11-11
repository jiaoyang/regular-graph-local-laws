import LocalLaw.GuardedObservationBias
import LocalLaw.SourceObservationDensity
import LocalLaw.SourceObservationParameters
import LocalLaw.ActualGuardedDeletionCaps
import LocalLaw.PolynomialDensityAbsorption

/-!
# The actual source one-edge observation bias

All Green caps, scalar tree identities, exceptional-edge counts, good-edge
existence, finite means and logarithmic absorptions are derived from the
actual plus event. The internal model radius is effective; every error is
the nominal source error.
-/

open Filter
noncomputable section
namespace LocalLaw
local instance sourceObservationMeanDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_sourceSingletonObservation_mean_bias (a b d : ℕ) (c β γ B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hγ : c / 4 < γ) (hgap : γ + β < 1)
    (hB : 0 ≤ B) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∀ Cq badCount : ℕ, badCount ≤ ⌊(N : ℝ) ^ γ⌋₊ →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      ‖finiteComplexMean (g.sourceSingletonObservation
          (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))
          (effectiveModelRadius a d N β) (logarithmicRadius (c / 4) d N / 4) z (g.Q z)) -
        (g.Q z - cavityIterate z (g.Q z) (effectiveModelRadius a d N β + 1))‖ ≤
          3 * graphPaperError a d N (logarithmicRadius β d N) z / Real.log (N : ℝ) ^ 16 := by
  let C := guardedGreenEntryCap d
  let P := sourceGreenPivotCap d B
  let M := C + C ^ 2 * P
  let BZ := DeficientGraph.singletonObservationConstant d * C1
  have hCref := finiteExtraReferenceConstant_ge_one d hd
  have hC : 0 ≤ C := by dsimp only [C, guardedGreenEntryCap, commonGreenEntryCap]; linarith
  have hP : 0 ≤ P := by
    have hC := finiteReferenceConstant_ge_one d hd
    dsimp only [P, sourceGreenPivotCap]
    positivity
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hC10 : 0 ≤ C1 := (by norm_num : (0 : ℝ) ≤ 1).trans hC1
  have hBZ : 0 ≤ BZ := by dsimp only [BZ, DeficientGraph.singletonObservationConstant]; positivity
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_sourceSingletonObservation_bound a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actualGuardedDeletionCaps a b d c β C1 B ha hb hd hc hβ hβc hC10 hB,
    eventually_ball_guarded_cavity_mean_bias_small a b d B C P ha hb hd hB hC hP,
    eventually_sourceBiasBadEdges_count a d c β γ (by omega) hd hc hβ hβc hγ,
    eventually_polynomial_density_absorbed a d 16 β γ (12 * (M + BZ)) hd hβ.le hgap,
    eventually_polynomial_density_absorbed a d 0 β γ 6 hd hβ.le hgap,
    eventually_paperError_small a b d β ha hb hd hβ,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_resampling_ball_budget a d hd, hdepth, eventually_log_ge_nat 2, eventually_ge_atTop 1]
    with N hZ hcaps hmean hbadCount hpoly hpoly6 herror hradii hball hdepth hlog hN
  intro g o z hz hzB hscale Cq badCount hbad hplus
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let ell := actualCavityDepth a d N z - 1
  let r := effectiveModelRadius a d N β
  let R := logarithmicRadius (c / 4) d N
  let T := graphBallVertices g.graph o ell
  let E := OutsideOrientedEdge g.graph T
  let bad := sourceBiasBadEdges g.graph T r (R / 4)
  let bZ := BZ * g.sourcePrime a (logarithmicRadius β d N) z
  have hL : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hε : 0 ≤ ε := graphPaperError_nonnegative a d N _ z hN hz.le
  have herr : ε ≤ (L ^ (4 * a))⁻¹ := herror z hz hscale
  have hscaled : ε * L ^ (4 * a) ≤ 1 :=
    (le_div_iff₀ (pow_pos hLp _)).mp (by simpa only [one_div] using herr)
  have hprime : 0 ≤ g.sourcePrime a (logarithmicRadius β d N) z := by
    change 0 ≤ L ^ 3 * ε
    positivity
  have hprimeOne : g.sourcePrime a (logarithmicRadius β d N) z ≤ 1 := by
    change L ^ 3 * ε ≤ 1
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (show 3 ≤ 4 * a by omega)) hε
    nlinarith only [hh, hscaled]
  have hbZ : 0 ≤ bZ := mul_nonneg hBZ hprime
  have hbZcap : bZ ≤ BZ := (mul_le_mul_of_nonneg_left hprimeOne hBZ).trans_eq (mul_one _)
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hT : 4 * Nat.card T ≤ N := by
    apply (Nat.mul_le_mul_left 4 ((g.ball_card_bound o ell).trans
      (Nat.pow_le_pow_right (by omega : 0 < d + 1) hell))).trans hball
  letI : Nonempty E := g.outside_edge_nonempty T (by omega) (by omega) hT
  have hbadActual : bad.card ≤ 3 * d * ⌊(N : ℝ) ^ γ⌋₊ :=
    hbadCount g o z (finiteOmega d) Cq badCount hbad hplus.structural
  have hfraction := g.outside_bad_edge_fraction_bound T (by omega) (by omega) hT bad γ hbadActual
  have hεlt : ε < 1 := by
    have hpow : 2 ≤ L ^ (4 * a) := hlog.trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hL (show 1 ≤ 4 * a by omega))
    have hh : ε * 2 ≤ 1 := (mul_le_mul_of_nonneg_left hpow hε).trans hscaled
    linarith
  have hsix : 6 * (N : ℝ) ^ γ / (N : ℝ) ≤ ε := by
    simpa only [pow_zero, div_one] using hpoly6 z hz.le
  have hcount : bad.card < Fintype.card E := finset_card_lt_of_fraction_lt_one bad
    (hfraction.trans_lt (hsix.trans_lt hεlt))
  have hmargin : r + 2 ≤ R / 4 := by have hh := hradii.2.2.2 z; dsimp only [r, R] at *; omega
  have caps := hcaps g o z hz hzB hscale Cq badCount hplus
  have hQ : ‖finiteComplexMean (outsideMatrixCavityValue g.graph T
      (guardedDeletedGreen g.H T (boundaryFarGuard g.graph T (R / 4 - 1)) z)) - g.Q z‖ ≤
      2 * ε / L ^ 16 := by
    simpa only [norm_sub_rev] using hmean g o ell (logarithmicRadius β d N)
      (boundaryFarGuard g.graph T (R / 4 - 1)) z hell hz hzB hscale caps
  have hZactual : ∀ e, ‖g.sourceSingletonObservation T r (R / 4) z (g.Q z) e‖ ≤ bZ := by
    intro e
    exact hZ g o z hz hscale hzB Cq badCount hplus e
  have hfinite := g.source_observation_bias_of_caps hd T R r hmargin (g.Q z) z hz
    (g.Q_im_nonnegative z hz) C P bZ (2 * ε / L ^ 16) hC hP caps hZactual hcount hQ
  have hbadCost : (Fintype.card E : ℝ)⁻¹ * (bad.card : ℝ) * (2 * (M + bZ)) ≤ ε / L ^ 16 := by
    calc
      _ ≤ (6 * (N : ℝ) ^ γ / (N : ℝ)) * (2 * (M + BZ)) :=
        mul_le_mul hfraction (by linarith only [hbZcap]) (by positivity)
          (by positivity)
      _ = (12 * (M + BZ)) * (N : ℝ) ^ γ / (N : ℝ) := by ring
      _ ≤ _ := hpoly z hz.le
  exact hfinite.trans ((add_le_add_right hbadCost _).trans_eq (by ring))

end RegularGraph
end LocalLaw
