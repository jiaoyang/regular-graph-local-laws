import LocalLaw.CycleReferenceKernel

/-!
# Relative cycle diagonal bounds for unicyclic leaf induction

The full-cycle return correction is at most three halves of md. Its diagonal
has a fixed positive fraction of |md|. Exact leaf reduction then contracts
the diagonal correction by |m|^2/(d-1), independently of attached-tree size.
-/

namespace LocalLaw

/-- A geometric cycle return has a uniformly controlled correction. -/
theorem cycle_return_correction_bound (p u : ℂ) (hu : ‖u‖ ≤ 27 / 64) :
    ‖p * (1 + u) / (1 - u) - p‖ ≤ (3 / 2 : ℝ) * ‖p‖ := by
  have hden : 37 / 64 ≤ ‖1 - u‖ := by
    have h := norm_sub_norm_le (1 : ℂ) u
    rw [norm_one] at h
    linarith
  have hne : 1 - u ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hden)
  have hid : p * (1 + u) / (1 - u) - p = (2 : ℂ) * p * u / (1 - u) := by
    field_simp [hne]
    ring
  rw [hid, norm_div, norm_mul, norm_mul]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ (2 * ‖p‖ * (27 / 64 : ℝ)) / (37 / 64 : ℝ) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hu (by positivity)) (by norm_num) hden
    _ ≤ (3 / 2 : ℝ) * ‖p‖ := by nlinarith [norm_nonneg p]

/-- The return factor cannot make the cycle diagonal small relative to md. -/
theorem cycle_return_relative_lower (p u : ℂ) (hu : ‖u‖ ≤ 1 / 2) :
    ‖p‖ / 4 ≤ ‖p * (1 + u) / (1 - u)‖ := by
  have hden : 1 / 2 ≤ ‖1 - u‖ := by
    have h := norm_sub_norm_le (1 : ℂ) u
    rw [norm_one] at h
    linarith
  have hnum : 1 / 2 ≤ ‖1 + u‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-u)
    rw [norm_one, norm_neg, sub_neg_eq_add] at h
    linarith
  have hupper : ‖1 - u‖ ≤ 3 / 2 := by
    have h := norm_sub_le (1 : ℂ) u
    rw [norm_one] at h
    linarith
  rw [norm_div, norm_mul]
  apply (le_div_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hden)).mpr
  have hp := norm_nonneg p
  have h₁ := mul_le_mul_of_nonneg_left hupper (show 0 ≤ ‖p‖ / 4 by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hnum hp
  nlinarith

theorem cycle_transfer_power_norm_sharp (n d : ℕ) (hd : 3 ≤ d) (m : ℂ) (hm : ‖m‖ ≤ 1) :
    ‖(-m * treeEdgeWeight d) ^ (n + 3)‖ ≤ 27 / 64 := by
  have ht := cycle_transfer_norm_le_three_quarters d hd m hm
  rw [norm_pow]
  calc
    _ ≤ (3 / 4 : ℝ) ^ (n + 3) := pow_le_pow_left₀ (norm_nonneg _) ht _
    _ ≤ (3 / 4 : ℝ) ^ 3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = _ := by norm_num

/-- Exact actual finite-cycle correction, ready for leaf-pruning induction. -/
theorem cycleReference_diagonal_deviation (n d : ℕ) (hd : 3 ≤ d) (z : ℂ)
    (hz : 0 < z.im) (i : Fin (n + 3)) :
    ‖(cycleReferenceMatrix n d (semicircleRoot z) z)⁻¹ i i -
        kestenMcKayTransform d (semicircleRoot z) z‖ ≤
      (3 / 2 : ℝ) * ‖kestenMcKayTransform d (semicircleRoot z) z‖ := by
  rw [cycleReferenceMatrix_inverse_diagonal n d hd z hz i]
  exact cycle_return_correction_bound _ _
    (cycle_transfer_power_norm_sharp n d hd _ (semicircleRoot_norm_le_one z))

theorem cycleReference_diagonal_relative_lower (n d : ℕ) (hd : 3 ≤ d) (z : ℂ)
    (hz : 0 < z.im) (i : Fin (n + 3)) :
    ‖kestenMcKayTransform d (semicircleRoot z) z‖ / 4 ≤
      ‖(cycleReferenceMatrix n d (semicircleRoot z) z)⁻¹ i i‖ := by
  rw [cycleReferenceMatrix_inverse_diagonal n d hd z hz i]
  exact cycle_return_relative_lower _ _
    (cycle_transfer_power_norm_le_half n d hd _ (semicircleRoot_norm_le_one z))

end LocalLaw
