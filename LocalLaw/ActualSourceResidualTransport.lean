import LocalLaw.ActualSwitchingQChange
import LocalLaw.SourceCavityResidual
import LocalLaw.CavityResidualTransport
import LocalLaw.SourceModelTransfer

/-!
# Actual finite residual transport to the retained weak target

The true cavity-average switching change is used with finite-depth feedback.
Every radius, denominator, scalar cap and logarithmic absorption is derived
from the source event, nominal error and bounded spectral domain.
-/

noncomputable section
namespace LocalLaw
local instance actualSourceResidualTransportDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceResidualFeedbackConstant (d : ℕ) (β B : ℝ) : ℝ :=
  2 * sourceObservationLogCap d β * cavityResidualTransportConstant B (sourceWidthConstant B)

namespace RegularGraph

theorem eventually_actual_source_residual_transport (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 1 ≤ C1) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      let gnew := g.labelledResampledGraph T labels samples (logarithmicRadius (c / 4) d N / 4)
      gnew.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (finiteOmega d) badCount z →
      ‖g.Q z - cavityIterate z (g.Q z) (effectiveModelRadius a d N β + 1)‖ ≤
        sourceResidualFeedbackConstant d β B * Real.log (N : ℝ) * gnew.sourceFeedback z +
          graphPaperError a d N (logarithmicRadius β d N) z / Real.log (N : ℝ) ^ 8 := by
  let A := sourceObservationLogCap d β
  let K := cavityResidualTransportConstant B (sourceWidthConstant B)
  let C := sourceResidualFeedbackConstant d β B
  have hA : 0 ≤ A := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hK : 0 ≤ K := by
    dsimp only [K, cavityResidualTransportConstant, sourceWidthConstant]
    positivity
  have hC : 0 ≤ C := by dsimp only [C, sourceResidualFeedbackConstant]; positivity
  have hC10 : 0 ≤ C1 := (by norm_num : (0 : ℝ) ≤ 1).trans hC1
  filter_upwards [eventually_actual_switching_Q_change a b d c β B C1 ha hb hd hc hβ hβc hC10 hB,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_kernel_feedback a b d β C1 1 1 ha hb hd hβ hC10 (by norm_num) (by norm_num),
    eventually_paperError_small a b d β ha hb hd hβ, eventually_log_ge_nat C]
    with N hchange hnum hfeedback herror hlarge
  intro g o z hz hzB hfloor Cq badCount hplus ι _ labels samples
  dsimp only
  let r := effectiveModelRadius a d N β
  let rn := logarithmicRadius β d N
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N rn z
  let τ := ε / L ^ 16
  let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
  let gnew := g.labelledResampledGraph T labels samples (logarithmicRadius (c / 4) d N / 4)
  intro htarget
  have num := hnum z hz hfloor
  have hε : 0 ≤ ε := num.error_nonnegative
  have hL : 1 ≤ L := num.log_one
  have hLp : 0 < L := by linarith
  have hτ : 0 ≤ τ := by dsimp only [τ]; positivity
  have hεOne : ε ≤ 1 := (herror z hz hfloor).trans
    ((inv_le_one₀ (pow_pos hLp _)).mpr (one_le_pow₀ hL))
  have hτOne : τ ≤ 1 := (div_le_one (pow_pos hLp _)).mpr (hεOne.trans (one_le_pow₀ hL))
  have hprior : ‖g.Q z - semicircleRoot z‖ ≤ C1 * scalarScale (spectralScale z) ε := hplus.cavity
  have hr : ((r + 1 : ℕ) : ℝ) ≤ 2 * (rn : ℝ) + 1 := by
    have hh : r ≤ rn := Nat.sub_le _ _
    exact_mod_cast (show r + 1 ≤ 2 * rn + 1 by omega)
  have hsmall : ((r + 1 : ℕ) : ℝ) * ‖g.Q z - semicircleRoot z‖ ≤ 1 / 2 := by
    have hh := hfeedback z (g.Q z) hz hfloor hprior
    simp only [mul_one] at hh
    exact (mul_le_mul_of_nonneg_right hr (norm_nonneg _)).trans (by simpa only [mul_comm] using hh)
  have hlength : ((r + 1 : ℕ) : ℝ) ≤ A * L := by
    have hh : (((4 * r + 1) + 1 : ℕ) : ℝ) ≤ A * L := by
      simpa only [Nat.cast_add, Nat.cast_one] using num.pair_log
    exact (Nat.cast_le.mpr (show r + 1 ≤ 4 * r + 1 + 1 by omega)).trans hh
  have hQ : ‖g.Q z - gnew.Q z‖ ≤ τ := hchange g o z hz hzB hfloor Cq badCount hplus labels samples htarget
  have hwidth : Real.sqrt (spectralScale z) ≤ sourceWidthConstant B := by
    simpa only [add_zero] using source_bounded_width B z 0 hzB (by norm_num)
  have hres := cavity_residual_feedback_near z (g.Q z) (gnew.Q z) hz B (sourceWidthConstant B) τ
    hzB hwidth hτ hτOne hQ (r + 1) hsmall
  have hF : 0 ≤ gnew.sourceFeedback z := by unfold sourceFeedback; positivity
  have hfirst : ‖g.Q z - cavityIterate z (g.Q z) (r + 1)‖ ≤ C * L * (gnew.sourceFeedback z + τ) := by
    apply hres.trans
    have hh := mul_le_mul_of_nonneg_right hlength
      (show 0 ≤ 2 * K * (gnew.sourceFeedback z + τ) by positivity)
    convert hh using 1 <;> dsimp only [C, sourceResidualFeedbackConstant, K, sourceFeedback] <;> ring
  have htail : C * L * τ ≤ ε / L ^ 8 := by
    have hCL : C * L ≤ L ^ 8 :=
      (mul_le_mul_of_nonneg_right hlarge hLp.le).trans
        (by simpa only [pow_two] using pow_le_pow_right₀ hL (show 2 ≤ 8 by omega))
    calc
      _ = (C * L * ε) / L ^ 16 := by dsimp only [τ]; ring
      _ ≤ (L ^ 8 * ε) / L ^ 16 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCL hε) (pow_nonneg hLp.le _)
      _ = ε / L ^ 8 := by field_simp; ring
  exact hfirst.trans (by nlinarith only [htail])

end RegularGraph
end LocalLaw
