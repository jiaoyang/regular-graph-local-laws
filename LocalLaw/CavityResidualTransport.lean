import LocalLaw.FiniteCavityResidual

/-! # Finite cavity residual in terms of the switched target feedback -/

namespace LocalLaw

noncomputable def cavityResidualTransportConstant (B S : ℝ) : ℝ :=
  2 + Real.sqrt (B + 2) + Real.sqrt (B + 2) * S

/-- The old residual uses target feedback plus the actual scalar switching
change. Only the old finite-depth denominator needs a smallness condition. -/
theorem cavity_residual_feedback_near (z q w : ℂ) (hz : 0 < z.im) (B S τ : ℝ)
    (hzB : ‖z‖ ≤ B) (hS : Real.sqrt (spectralScale z) ≤ S)
    (hτ : 0 ≤ τ) (hτOne : τ ≤ 1) (hqw : ‖q - w‖ ≤ τ)
    (n : ℕ) (hsmall : (n : ℝ) * ‖q - semicircleRoot z‖ ≤ 1 / 2) :
    ‖q - cavityIterate z q n‖ ≤ 2 * (n : ℝ) * cavityResidualTransportConstant B S *
      (Real.sqrt (spectralScale z) * ‖w - semicircleRoot z‖ +
        ‖w - semicircleRoot z‖ ^ 2 + τ) := by
  let δ := ‖q - semicircleRoot z‖
  let ξ := ‖w - semicircleRoot z‖
  let a := Real.sqrt (B + 2)
  let s := Real.sqrt (spectralScale z)
  let K := cavityResidualTransportConstant B S
  have hS0 : 0 ≤ S := (Real.sqrt_nonneg _).trans hS
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hδ : 0 ≤ δ := norm_nonneg _
  have hξ : 0 ≤ ξ := norm_nonneg _
  have hnear : δ ≤ ξ + τ :=
    (norm_sub_le_norm_sub_add_norm_sub q w (semicircleRoot z)).trans
      ((add_le_add_right hqw ξ).trans_eq (add_comm _ _))
  have hδsq : δ ^ 2 ≤ 2 * ξ ^ 2 + 2 * τ := by
    have hp := pow_le_pow_left₀ hδ hnear 2
    have hτsq : τ ^ 2 ≤ τ := by nlinarith only [mul_nonneg hτ (show 0 ≤ 1 - τ by linarith)]
    nlinarith only [hp, hτsq, sq_nonneg (ξ - τ)]
  have hδs : a * s * δ ≤ a * s * ξ + a * S * τ := by
    have hh := mul_le_mul_of_nonneg_left hnear (show 0 ≤ a * s by positivity)
    have ht := mul_le_mul_of_nonneg_left hS (show 0 ≤ a * τ by positivity)
    nlinarith only [hh, ht]
  have hKtwo : 2 ≤ K := by
    dsimp only [K, cavityResidualTransportConstant]
    linarith only [Real.sqrt_nonneg (B + 2), mul_nonneg (Real.sqrt_nonneg (B + 2)) hS0]
  have hKa : a ≤ K := by dsimp only [K, cavityResidualTransportConstant]; nlinarith only [ha, mul_nonneg ha hS0]
  have hKt : 2 + a * S ≤ K := by dsimp only [K, cavityResidualTransportConstant]; linarith only [ha]
  have hsum : δ ^ 2 + a * s * δ ≤ K * (s * ξ + ξ ^ 2 + τ) := by
    have hsq := mul_le_mul_of_nonneg_right hKtwo (sq_nonneg ξ)
    have hlin := mul_le_mul_of_nonneg_right hKa (show 0 ≤ s * ξ by positivity)
    have ht := mul_le_mul_of_nonneg_right hKt hτ
    nlinarith only [hδsq, hδs, hsq, hlin, ht]
  exact (cavity_residual_feedback z q hz B hzB n hsmall).trans
    ((mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * (n : ℝ))).trans_eq (by ring))

end LocalLaw
