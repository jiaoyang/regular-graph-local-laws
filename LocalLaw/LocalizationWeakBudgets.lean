import LocalLaw.FiniteLocalization
import LocalLaw.ScalarStability

/-!
# Explicit finite localization budgets from a weak local-law prior

The physical weak prior bounds both square-root and quadratic feedback.
An error with epsilon*L^4<=1 and logarithmic diameter caps realizes every
finite smallness condition in the actual localization theorem once L exceeds
a fixed degree/domain/diameter constant.
-/

noncomputable section
namespace LocalLaw

theorem scale_weight_small (x L H : ℝ) (_hx : 0 ≤ x) (hL : 0 < L) (hH : 0 ≤ H)
    (hscale : x * L ^ 2 ≤ 1) (hlarge : 2 * H ≤ L) : x * H * L ≤ 1 / 2 := by
  apply (mul_le_mul_right hL).mp
  have hh := mul_le_mul_of_nonneg_left hscale hH
  nlinarith

theorem weak_prior_scaled_norm (z q : ℂ) (hz : 0 < z.im) (ε L : ℝ)
    (hε : 0 ≤ ε) (hcap : ε * L ^ 4 ≤ 1)
    (hprior : ‖q - semicircleRoot z‖ ≤ scalarScale (spectralScale z) ε) :
    ‖q - semicircleRoot z‖ * L ^ 2 ≤ 1 := by
  have hs := spectralScale_pos hz
  have hp := hprior.trans (scalarScale_le_sqrt hs hε)
  have hsq : (Real.sqrt ε * L ^ 2) ^ 2 = ε * L ^ 4 := by
    rw [mul_pow, Real.sq_sqrt hε]
    ring
  have hr : Real.sqrt ε * L ^ 2 ≤ 1 := by
    have hh : (Real.sqrt ε * L ^ 2) ^ 2 ≤ 1 := by rw [hsq]; exact hcap
    have hn : 0 ≤ Real.sqrt ε * L ^ 2 := by positivity
    nlinarith
  exact (mul_le_mul_of_nonneg_right hp (sq_nonneg L)).trans hr

theorem weak_boundary_norm_le_two (z q : ℂ) (hz : 0 < z.im) (ε : ℝ)
    (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hprior : ‖q - semicircleRoot z‖ ≤ scalarScale (spectralScale z) ε) : ‖q‖ ≤ 2 := by
  have hroot : Real.sqrt ε ≤ 1 := by simpa using Real.sqrt_le_sqrt hεone
  have hδ := hprior.trans (scalarScale_le_sqrt (spectralScale_pos hz) hε)
  have htri := norm_add_le (q - semicircleRoot z) (semicircleRoot z)
  rw [sub_add_cancel] at htri
  linarith [semicircleRoot_norm_le_one z]

namespace DeficientGraph

def localizationBudgetConstant (d : ℕ) (B A : ℝ) : ℝ :=
  let C := finiteExtraReferenceConstant d
  let C₀ := coreConvolutionConstant (finiteOmega d + 1)
  2 * (A * (2 * (finiteOmega d : ℝ) + 3) * C * C₀ + 9 * A +
    4 * A ^ 2 * (Real.sqrt (B + 2) + 128) * C * C₀)

def localizationWeakConstant (d : ℕ) (B A : ℝ) : ℝ :=
  let C := finiteExtraReferenceConstant d
  let C₀ := coreConvolutionConstant (finiteOmega d + 1)
  64 * A * (Real.sqrt (B + 2) + 128) * C ^ 2 * C₀ +
    8 * C ^ 2 * localizationExceptionalMass d (2 : ℂ) +
    8 * C ^ 2 * (((finiteOmega d : ℝ) + 1) / ((d : ℝ) - 1)) + 2 * C + 1

theorem ordinaryFeedbackBudget_le_of_weak (z q : ℂ) (hz : 0 < z.im)
    (B ε : ℝ) (R : ℕ) (hε : 0 ≤ ε)
    (hprior : ‖q - semicircleRoot z‖ ≤ scalarScale (spectralScale z) ε) :
    ordinaryFeedbackBudget z q B R ≤ ((2 * R : ℕ) + 1 : ℝ) *
      (Real.sqrt (B + 2) + 128) * ε := by
  have hs := spectralScale_pos hz
  have hlinear := (mul_le_mul_of_nonneg_left hprior (Real.sqrt_nonneg (spectralScale z))).trans
    (scalarScale_sqrt_mul_le hs hε)
  have hquad := (pow_le_pow_left₀ (norm_nonneg _) hprior 2).trans (scalarScale_sq_le hs hε)
  unfold ordinaryFeedbackBudget
  calc
    _ = ((2 * R : ℕ) + 1 : ℝ) *
        (Real.sqrt (B + 2) * (Real.sqrt (spectralScale z) * ‖q - semicircleRoot z‖) +
          128 * ‖q - semicircleRoot z‖ ^ 2) := by ring
    _ ≤ ((2 * R : ℕ) + 1 : ℝ) * (Real.sqrt (B + 2) * ε + 128 * ε) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hlinear (Real.sqrt_nonneg (B + 2)))
          (mul_le_mul_of_nonneg_left hquad (by norm_num : (0 : ℝ) ≤ 128))) (by positivity)
    _ = _ := by ring

theorem ordinaryFeedbackBudget_log_cap (z q : ℂ) (hz : 0 < z.im)
    (B ε L A : ℝ) (R : ℕ) (hε : 0 ≤ ε)
    (hprior : ‖q - semicircleRoot z‖ ≤ scalarScale (spectralScale z) ε)
    (hR : (R : ℝ) + 1 ≤ A * L) :
    ordinaryFeedbackBudget z q B R ≤ 2 * A * (Real.sqrt (B + 2) + 128) * L * ε := by
  apply (ordinaryFeedbackBudget_le_of_weak z q hz B ε R hε hprior).trans
  have hK : 0 ≤ (Real.sqrt (B + 2) + 128) * ε := by positivity
  have hh := mul_le_mul_of_nonneg_right hR hK
  push_cast
  nlinarith only [hh, hK]

theorem weak_localization_feedback_budgets (d : ℕ) (hd : 3 ≤ d)
    (z q : ℂ) (hz : 0 < z.im) (B ε L A : ℝ)
    (hε : 0 ≤ ε) (hL : 1 ≤ L) (hA : 0 ≤ A) (hcap : ε * L ^ 4 ≤ 1)
    (hprior : ‖q - semicircleRoot z‖ ≤ scalarScale (spectralScale z) ε)
    (R Rs : ℕ) (hR : (R : ℝ) + 1 ≤ A * L) (hRs : (Rs : ℝ) + 1 ≤ A * L)
    (hlarge : localizationBudgetConstant d B A ≤ L) :
    (‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2) ∧
    (‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((Rs : ℝ) + 1) ≤ 1 / 2) ∧
    (‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * (((finiteOmega d + 1) * (2 * R + 1) : ℕ) + 1 : ℝ) ≤ 1 / 2) ∧
    (‖q - semicircleRoot z‖ * 3 * (3 / 2 : ℝ) * ((2 * R : ℕ) + 1 : ℝ) ≤ 1 / 2) ∧
    (ordinaryFeedbackBudget z q B R * (2 * finiteExtraReferenceConstant d) *
      coreConvolutionConstant (finiteOmega d + 1) * ((Rs : ℝ) + 1) ≤ 1 / 2) := by
  let C := finiteExtraReferenceConstant d
  let C₀ := coreConvolutionConstant (finiteOmega d + 1)
  let K := Real.sqrt (B + 2) + 128
  let Hout := A * (2 * (finiteOmega d : ℝ) + 3) * C * C₀
  let Hcavity := 9 * A
  let Hordinary := 4 * A ^ 2 * K * C * C₀
  have hC : 0 ≤ C := le_trans (by norm_num) (finiteExtraReferenceConstant_ge_one d hd)
  have hC₀ : 0 ≤ C₀ := coreConvolutionConstant_nonnegative _
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hHout : 0 ≤ Hout := by dsimp only [Hout]; positivity
  have hHcavity : 0 ≤ Hcavity := by dsimp only [Hcavity]; positivity
  have hHordinary : 0 ≤ Hordinary := by dsimp only [Hordinary]; positivity
  have hsum : 2 * (Hout + Hcavity + Hordinary) ≤ L := hlarge
  have hlargeOut : 2 * Hout ≤ L := by linarith
  have hlargeCavity : 2 * Hcavity ≤ L := by linarith
  have hlargeOrdinary : 2 * Hordinary ≤ L ^ 2 := by
    have hh : 2 * Hordinary ≤ L := by linarith only [hsum, hHout, hHcavity]
    exact hh.trans (by nlinarith only [hL])
  have hLpos : 0 < L := by linarith
  have hnorm := weak_prior_scaled_norm z q hz ε L hε hcap hprior
  have hδ : 0 ≤ ‖q - semicircleRoot z‖ := norm_nonneg _
  have hscaleOut := scale_weight_small _ L Hout hδ hLpos hHout hnorm hlargeOut
  have hscaleCavity := scale_weight_small _ L Hcavity hδ hLpos hHcavity hnorm hlargeCavity
  have hscaleOrdinary := scale_weight_small ε (L ^ 2) Hordinary hε (sq_pos_of_pos hLpos) hHordinary
    (by convert hcap using 1; ring) hlargeOrdinary
  have hfactor : 1 ≤ 2 * (finiteOmega d : ℝ) + 3 := by
    have hn := Nat.cast_nonneg (α := ℝ) (finiteOmega d)
    linarith only [hn]
  have hcapR : (R : ℝ) + 1 ≤ A * (2 * (finiteOmega d : ℝ) + 3) * L := by
    apply hR.trans
    exact (le_mul_of_one_le_right (mul_nonneg hA hLpos.le) hfactor).trans_eq (by ring)
  have hcapRs : (Rs : ℝ) + 1 ≤ A * (2 * (finiteOmega d : ℝ) + 3) * L := by
    apply hRs.trans
    exact (le_mul_of_one_le_right (mul_nonneg hA hLpos.le) hfactor).trans_eq (by ring)
  have hcapOutside : (((finiteOmega d + 1) * (2 * R + 1) : ℕ) + 1 : ℝ) ≤
      A * (2 * (finiteOmega d : ℝ) + 3) * L := by
    have hh := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 2 * (finiteOmega d : ℝ) + 3)
    have hgeom : (((finiteOmega d + 1) * (2 * R + 1) : ℕ) + 1 : ℝ) ≤
        (2 * (finiteOmega d : ℝ) + 3) * ((R : ℝ) + 1) := by
      push_cast
      nlinarith only [Nat.cast_nonneg (α := ℝ) (finiteOmega d), Nat.cast_nonneg (α := ℝ) R]
    exact hgeom.trans (hh.trans_eq (by ring))
  have hrefsmall (D : ℝ) (hD : D ≤ A * (2 * (finiteOmega d : ℝ) + 3) * L) :
      ‖q - semicircleRoot z‖ * C * C₀ * D ≤ 1 / 2 := by
    calc
      _ ≤ ‖q - semicircleRoot z‖ * C * C₀ * (A * (2 * (finiteOmega d : ℝ) + 3) * L) :=
        mul_le_mul_of_nonneg_left hD (mul_nonneg (mul_nonneg hδ hC) hC₀)
      _ = ‖q - semicircleRoot z‖ * Hout * L := by dsimp only [Hout]; ring
      _ ≤ _ := hscaleOut
  refine ⟨hrefsmall _ hcapR, hrefsmall _ hcapRs, hrefsmall _ hcapOutside, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hR (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) hδ)
    apply le_trans _ hscaleCavity
    dsimp only [Hcavity]
    push_cast
    nlinarith only [hh, hδ]
  · have hτ := ordinaryFeedbackBudget_le_of_weak z q hz B ε R hε hprior
    have hτcap : ordinaryFeedbackBudget z q B R ≤ 2 * A * K * L * ε := by
      apply hτ.trans
      have hh := mul_le_mul_of_nonneg_right hR (mul_nonneg hK hε)
      change ((2 * R : ℕ) + 1 : ℝ) * K * ε ≤ _
      have hnonneg := mul_nonneg hK hε
      push_cast
      nlinarith only [hh, hnonneg]
    have hleft := mul_le_mul_of_nonneg_right hτcap (mul_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC) hC₀)
    have hright := mul_le_mul hleft hRs (by positivity : 0 ≤ (Rs : ℝ) + 1)
      (by positivity : 0 ≤ (2 * A * K * L * ε) * (2 * C * C₀))
    calc
      _ = (ordinaryFeedbackBudget z q B R * (2 * C * C₀)) * ((Rs : ℝ) + 1) := by ring
      _ ≤ (2 * A * K * L * ε * (2 * C * C₀)) * (A * L) := hright
      _ = ε * Hordinary * (L ^ 2) := by dsimp only [Hordinary]; ring
      _ ≤ _ := hscaleOrdinary

/-- The complete localization expression, including the disconnected-pair
tail, is at most a fixed constant times L*epsilon under the weak prior. -/
theorem localization_expression_weak_rate (d : ℕ) (hd : 3 ≤ d)
    (z q : ℂ) (hz : 0 < z.im) (B ε L A : ℝ)
    (hε : 0 ≤ ε) (hεone : ε ≤ 1) (hL : 1 ≤ L) (_hA : 0 ≤ A)
    (hprior : ‖q - semicircleRoot z‖ ≤ scalarScale (spectralScale z) ε)
    (R r : ℕ) (hR : (R : ℝ) + 1 ≤ A * L)
    (htail : physicalTransfer d z ^ (2 * r) ≤ ε) :
    32 * finiteExtraReferenceConstant d ^ 2 * coreConvolutionConstant (finiteOmega d + 1) *
        ordinaryFeedbackBudget z q B R +
      (8 * finiteExtraReferenceConstant d ^ 2 * localizationExceptionalMass d q +
        4 * finiteExtraReferenceConstant d ^ 2 * ‖q‖ *
          (((finiteOmega d : ℝ) + 1) / ((d : ℝ) - 1)) + 2 * finiteExtraReferenceConstant d) *
        physicalTransfer d z ^ (2 * r) ≤ localizationWeakConstant d B A * L * ε := by
  let C := finiteExtraReferenceConstant d
  let C₀ := coreConvolutionConstant (finiteOmega d + 1)
  let tail := physicalTransfer d z ^ (2 * r)
  let H := 8 * C ^ 2 * localizationExceptionalMass d (2 : ℂ) +
    8 * C ^ 2 * (((finiteOmega d : ℝ) + 1) / ((d : ℝ) - 1)) + 2 * C
  let P := 64 * A * (Real.sqrt (B + 2) + 128) * C ^ 2 * C₀
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hk : 0 < (d : ℝ) - 1 := by linarith
  have hC : 0 ≤ C := le_trans (by norm_num) (finiteExtraReferenceConstant_ge_one d hd)
  have hC₀ : 0 ≤ C₀ := coreConvolutionConstant_nonnegative _
  have hq := weak_boundary_norm_le_two z q hz ε hε hεone hprior
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  have hM : localizationExceptionalMass d q ≤ localizationExceptionalMass d (2 : ℂ) := by
    unfold localizationExceptionalMass
    rw [htwo]
    apply div_le_div_of_nonneg_right _ hk.le
    exact add_le_add_left (mul_le_mul_of_nonneg_right hq (by positivity)) _
  have hMnonneg : 0 ≤ localizationExceptionalMass d (2 : ℂ) := by
    unfold localizationExceptionalMass
    positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have htail0 : 0 ≤ tail := pow_nonneg (physicalTransfer_pos d hd z).le _
  have hcoef : 8 * C ^ 2 * localizationExceptionalMass d q +
      4 * C ^ 2 * ‖q‖ * (((finiteOmega d : ℝ) + 1) / ((d : ℝ) - 1)) + 2 * C ≤ H := by
    have hfirst := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 8 * C ^ 2)
    have hsecond := mul_le_mul_of_nonneg_right hq
      (by positivity : 0 ≤ 4 * C ^ 2 * (((finiteOmega d : ℝ) + 1) / ((d : ℝ) - 1)))
    dsimp only [H]
    nlinarith only [hfirst, hsecond]
  have hfirst : 32 * C ^ 2 * C₀ * ordinaryFeedbackBudget z q B R ≤ P * L * ε := by
    have hh := mul_le_mul_of_nonneg_left (ordinaryFeedbackBudget_log_cap z q hz B ε L A R hε hprior hR)
      (by positivity : 0 ≤ 32 * C ^ 2 * C₀)
    exact hh.trans_eq (by dsimp only [P]; ring)
  have hlast : (8 * C ^ 2 * localizationExceptionalMass d q +
      4 * C ^ 2 * ‖q‖ * (((finiteOmega d : ℝ) + 1) / ((d : ℝ) - 1)) + 2 * C) * tail ≤ H * ε :=
    (mul_le_mul_of_nonneg_right hcoef htail0).trans (mul_le_mul_of_nonneg_left htail hH)
  have hεL : ε ≤ L * ε := le_mul_of_one_le_left hε hL
  have htailL := mul_le_mul_of_nonneg_left hεL hH
  change _ ≤ localizationWeakConstant d B A * L * ε
  calc
    _ ≤ P * L * ε + H * ε := add_le_add hfirst hlast
    _ ≤ P * L * ε + H * (L * ε) := add_le_add_left htailL _
    _ ≤ (P + H + 1) * L * ε := by nlinarith only [mul_nonneg (by linarith : 0 ≤ L) hε]
    _ = _ := by dsimp only [localizationWeakConstant, P, H, C, C₀]; ring

end DeficientGraph
end LocalLaw
