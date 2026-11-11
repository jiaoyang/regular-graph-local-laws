import LocalLaw.SourceDeletedVariance
import LocalLaw.BoundaryPerturbationParameters
import LocalLaw.EffectiveModelRadius

/-! # Actual source F2 correlation probability without model-cap inputs

The effective local radius fits the common original neighborhood also at
beta=c/32. Its deleted reference class gives the diagonal variance cap;
the nominal source error realizes boundary-feedback smallness. The actual
Ward identity, endpoint counting, and independent sample tail then give
the simultaneous F2 failure bound with no reference or variance hypothesis.
-/

noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw

local instance sourceCorrelationProbabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem eventually_sourceOmegaPlusWithRadii_few_correlated_samples
    (a b d q : ℕ) (c β C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d)
    (hc : 0 < c) (hc₁ : c < 1) (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 0 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      eventMass (localSamplingWeight g.graph T)
        (fun S => ∃ x : {w : Fin N // w ∉ T}, Nat.ceil (Real.log (N : ℝ)) ≤
          (g.correlatedSampleIndices T z
            (correlationThreshold (Real.log (N : ℝ)) a N z.im
              (graphKestenMcKayReference d z).im (spectralScale z)
                (graphPaperError a d N (logarithmicRadius β d N) z))
            (logarithmicRadius (c / 4) d N / 4) x S).card) ≤ 1 / (N : ℝ) ^ q := by
  have ha0 : 0 < a := by omega
  let C := finiteExtraReferenceConstant d
  let C₀ := coreConvolutionConstant (finiteOmega d + 1)
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hC₀ : 0 ≤ C₀ := coreConvolutionConstant_nonnegative (finiteOmega d + 1)
  have hfeedback := eventually_source_kernel_feedback a b d β C1 (2 * C) C₀
    ha hb hd hβ hC1 (by positivity) hC₀
  have hdepth := (lowerLogLogRadius_tendsto a d ha0 hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_uniform_few_correlated_samples a d q c (sourceDeletedVarianceConstant C1 d)
    ha0 hd hc.le hc₁ (sourceDeletedVarianceConstant_nonnegative C1 d hC1 hd),
    hfeedback, eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    hdepth, eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1] with
      N htail hfeedback hmargin hdepth hlog hN
  intro g o z hz hscale Cq badCount hplus
  dsimp only
  let r := effectiveModelRadius a d N β
  let rn := logarithmicRadius β d N
  let R := logarithmicRadius (c / 4) d N
  let ell := actualCavityDepth a d N z - 1
  let ε := graphPaperError a d N rn z
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hfit : r + 2 * ell + 1 ≤ R / 8 := by dsimp only [r, R]; omega
  have hrn : r ≤ rn := Nat.sub_le _ _
  have hsmall : ‖g.Q z - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * (4 * (r : ℝ) + 2) ≤ 1 / 2 := by
    have hh := hfeedback z (g.Q z) hz hscale hplus.cavity
    have hcast : (r : ℝ) ≤ rn := Nat.cast_le.mpr hrn
    calc
      _ ≤ ‖g.Q z - semicircleRoot z‖ * C * C₀ * (2 * (2 * (rn : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ‖g.Q z - semicircleRoot z‖ * (2 * C) * C₀ * (2 * (rn : ℝ) + 1) := by ring
      _ ≤ 1 / 2 := hh
  have hcap := hplus.actual_diagonal_variance_cap hN hd hz hC1 hfit hsmall
  have hv : 0 ≤ (graphKestenMcKayReference d z).im :=
    (kestenMcKayTransform_im_pos d (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le).le
  have hLp : 0 < Real.log (N : ℝ) := by linarith
  have hk : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hfloor : 0 < localizationErrorFloor a d N rn := by unfold localizationErrorFloor; positivity
  have hε : 0 < ε := hfloor.trans_le (graphPaperError_lower a d N rn z hlog hz.le)
  exact htail g o z hz (graphKestenMcKayReference d z).im (spectralScale z) ε hv hε hcap

end LocalLaw
