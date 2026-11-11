import LocalLaw.ScalarRecursion
import LocalLaw.ScalarStability
import LocalLaw.SpectralGap
import LocalLaw.Semicircle

/-!
# The finite-depth cavity residual has the quadratic feedback scale

The denominator is controlled at the actual finite depth. Near an edge the
iteration is too short to contract to the fixed point, so its residual is
of order depth times the squared weak displacement, rather than that weak
displacement itself.
-/

namespace LocalLaw

theorem cavity_residual_feedback (z q : ℂ) (hz : 0 < z.im) (B : ℝ) (hzB : ‖z‖ ≤ B)
    (n : ℕ) (hsmall : (n : ℝ) * ‖q - semicircleRoot z‖ ≤ 1 / 2) :
    ‖q - cavityIterate z q n‖ ≤ 2 * (n : ℝ) *
      (‖q - semicircleRoot z‖ ^ 2 + Real.sqrt (B + 2) * Real.sqrt (spectralScale z) *
        ‖q - semicircleRoot z‖) := by
  let m := semicircleRoot z
  let δ := ‖q - m‖
  let poly := ‖q ^ 2 + z * q + 1‖
  have hm := semicircleRoot_equation z
  have hmnorm := semicircleRoot_norm_le_one z
  have hden := (cavityDenominator_bounds hmnorm n hsmall).1
  have hid := congrArg norm (cavity_residual_identity_of_small hm hmnorm n hsmall)
  simp only [norm_mul, norm_neg] at hid
  have hsum : ‖m‖ * ‖cavitySum m n‖ ≤ (n : ℝ) := by
    calc
      _ ≤ 1 * (n : ℝ) := mul_le_mul hmnorm (cavitySum_norm_le hmnorm n) (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hres : ‖q - cavityIterate z q n‖ ≤ 2 * (n : ℝ) * poly := by
    have hlow := mul_le_mul_of_nonneg_right hden (norm_nonneg (q - cavityIterate z q n))
    have hupp := mul_le_mul_of_nonneg_right hsum (norm_nonneg (q ^ 2 + z * q + 1))
    change _ ≤ (n : ℝ) * poly at hupp
    change _ * ‖q - cavityIterate z q n‖ = _ * poly at hid
    nlinarith only [hlow, hupp, hid]
  have hgap := (cavity_root_gap_bounds hm hz hzB).2
  have hpoly : poly ≤ δ ^ 2 + Real.sqrt (B + 2) * Real.sqrt (spectralScale z) * δ := by
    rw [show poly = ‖(q - m) * ((q - m) - (m⁻¹ - m))‖ by
      dsimp only [poly, m]; rw [cavity_quadratic_factor hm]]
    rw [norm_mul]
    calc
      _ ≤ δ * (δ + ‖m⁻¹ - m‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ δ * (δ + Real.sqrt (B + 2) * Real.sqrt (spectralScale z)) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hgap δ) (norm_nonneg _)
      _ = _ := by ring
  exact hres.trans (mul_le_mul_of_nonneg_left hpoly (by positivity))

/-- A weak prior controls both the stable and edge contributions to the
finite residual. The scalar error is independent of the iteration depth. -/
theorem cavity_residual_of_weak_prior (z q : ℂ) (hz : 0 < z.im)
    (B ε C : ℝ) (hzB : ‖z‖ ≤ B) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hprior : ‖q - semicircleRoot z‖ ≤ C * scalarScale (spectralScale z) ε)
    (n : ℕ) (hsmall : (n : ℝ) * ‖q - semicircleRoot z‖ ≤ 1 / 2) :
    ‖q - cavityIterate z q n‖ ≤ 2 * (n : ℝ) *
      (C ^ 2 + Real.sqrt (B + 2) * C) * ε := by
  let δ := ‖q - semicircleRoot z‖
  let Ψ := scalarScale (spectralScale z) ε
  have hs := spectralScale_pos hz
  have hΨ : 0 ≤ Ψ := scalarScale_nonneg hε
  have hδsq : δ ^ 2 ≤ C ^ 2 * ε := by
    calc
      _ ≤ (C * Ψ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hprior 2
      _ = C ^ 2 * Ψ ^ 2 := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (scalarScale_sq_le hs hε) (sq_nonneg C)
  have hδs : Real.sqrt (spectralScale z) * δ ≤ C * ε := by
    calc
      _ ≤ Real.sqrt (spectralScale z) * (C * Ψ) := mul_le_mul_of_nonneg_left hprior (Real.sqrt_nonneg _)
      _ = C * (Real.sqrt (spectralScale z) * Ψ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (scalarScale_sqrt_mul_le hs hε) hC
  have hfeedback : δ ^ 2 + Real.sqrt (B + 2) * Real.sqrt (spectralScale z) * δ ≤
      (C ^ 2 + Real.sqrt (B + 2) * C) * ε := by
    have hh := mul_le_mul_of_nonneg_left hδs (Real.sqrt_nonneg (B + 2))
    nlinarith only [hδsq, hh]
  exact (cavity_residual_feedback z q hz B hzB n hsmall).trans
    ((mul_le_mul_of_nonneg_left hfeedback (by positivity : 0 ≤ 2 * (n : ℝ))).trans_eq (by ring))

end LocalLaw
