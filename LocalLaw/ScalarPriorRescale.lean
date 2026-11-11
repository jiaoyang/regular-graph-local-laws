import LocalLaw.ScalarStability

/-!
# Absorbing a fixed scalar-prior constant in the error budget

Only the numerical weak error is enlarged. Model radii and the original
paper-error definition are unchanged.
-/

namespace LocalLaw

theorem scalarScale_constant_absorption (s ε C : ℝ) (hs : 0 < s) (hε : 0 ≤ ε)
    (hC : 1 ≤ C) : C * scalarScale s ε ≤ scalarScale s (C ^ 2 * ε) := by
  have hC0 : 0 ≤ C := by linarith
  have hC2 : 1 ≤ C ^ 2 := by nlinarith
  have hroot : Real.sqrt (s + C ^ 2 * ε) ≤ C * Real.sqrt (s + ε) := by
    calc
      _ ≤ Real.sqrt (C ^ 2 * (s + ε)) := Real.sqrt_le_sqrt (by nlinarith)
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq_eq_abs, abs_of_nonneg hC0]
  have hmul := mul_le_mul_of_nonneg_left hroot (mul_nonneg hC0 hε)
  unfold scalarScale
  simp only [← mul_div_assoc]
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr (by linarith))
    (Real.sqrt_pos.mpr (by positivity))).mpr
  convert hmul using 1; ring

end LocalLaw
