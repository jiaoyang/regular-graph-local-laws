import LocalLaw.LocalizationWeakBudgets

/-! # The actual quadratic defect supplied by a weak physical-root prior -/

noncomputable section
namespace LocalLaw

theorem weak_prior_quadratic_defect (q z : ℂ) (hz : 0<z.im) (B ε : ℝ)
    (hzB : ‖z‖≤B) (hε : 0≤ε)
    (hprior : ‖q-semicircleRoot z‖≤scalarScale (spectralScale z) ε) :
    ‖1+z*q+q^2‖≤(Real.sqrt (B+2)+1)*ε := by
  let m:=semicircleRoot z
  let δ:=‖q-m‖
  have hlin := (mul_le_mul_of_nonneg_left hprior (Real.sqrt_nonneg (spectralScale z))).trans
    (scalarScale_sqrt_mul_le (spectralScale_pos hz) hε)
  have hquad := (pow_le_pow_left₀ (norm_nonneg _) hprior 2).trans
    (scalarScale_sq_le (spectralScale_pos hz) hε)
  have hgap := (cavity_root_gap_bounds (semicircleRoot_equation z) hz hzB).2
  have he : 1+z*q+q^2=q^2+z*q+1 := by ring
  rw [he,cavity_quadratic_factor (semicircleRoot_equation z),norm_mul]
  calc
    _≤δ*(δ+‖m⁻¹-m‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _≤δ*(δ+Real.sqrt (B+2)*Real.sqrt (spectralScale z)) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hgap δ) (norm_nonneg _)
    _≤(Real.sqrt (B+2)+1)*ε := by
      dsimp only [δ,m] at *
      nlinarith only [hquad,mul_le_mul_of_nonneg_left hlin (Real.sqrt_nonneg (B+2))]

theorem weak_prior_quadratic_defect_div (q z : ℂ) (hz : 0<z.im) (B ε K : ℝ)
    (hzB : ‖z‖≤B) (hε : 0≤ε)
    (hprior : ‖q-semicircleRoot z‖≤scalarScale (spectralScale z) ε)
    (_hK : 0≤K) (hqinv : ‖q⁻¹‖≤K) :
    ‖(1+z*q+q^2)/q‖≤K*(Real.sqrt (B+2)+1)*ε := by
  rw [div_eq_mul_inv,norm_mul]
  exact (mul_le_mul (weak_prior_quadratic_defect q z hz B ε hzB hε hprior) hqinv
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

end LocalLaw
