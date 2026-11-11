import Mathlib

/-!
# One-vertex Schur stability from pivot ratios

The reference full Green entries may be large. Only the reciprocal reference
pivot and its two normalized cross entries are bounded. A small entry error
then gives a bounded actual pivot transfer and a uniform deleted-entry error.
-/

namespace LocalLaw

theorem scalar_pivot_transfer (d D : ℂ) (L δ : ℝ) (hD : D ≠ 0) (hδ : 0 ≤ δ)
    (hinv : ‖D⁻¹‖ ≤ L) (hdiff : ‖d - D‖ ≤ δ) (hsmall : L * δ ≤ 1 / 2) :
    d ≠ 0 ∧ ‖d⁻¹‖ ≤ 2 * L ∧ ‖D / d‖ ≤ 2 := by
  have hDp : 0 < ‖D‖ := norm_pos_iff.mpr hD
  have hinvR : ‖D‖⁻¹ ≤ L := by simpa only [norm_inv] using hinv
  have hrelative : δ / ‖D‖ ≤ 1 / 2 := by
    calc
      _ = δ * ‖D‖⁻¹ := div_eq_mul_inv _ _
      _ ≤ δ * L := mul_le_mul_of_nonneg_left hinvR hδ
      _ ≤ 1 / 2 := by nlinarith
  have hδD : δ ≤ ‖D‖ / 2 := by
    have hh := (div_le_iff₀ hDp).mp hrelative
    linarith
  have htriangle : ‖D‖ ≤ ‖d‖ + δ := by
    have hh := norm_add_le (D - d) d
    rw [sub_add_cancel, norm_sub_rev] at hh
    linarith
  have hdp : 0 < ‖d‖ := by linarith
  have hd : d ≠ 0 := norm_pos_iff.mp hdp
  have hactualInv : ‖d⁻¹‖ ≤ 2 * L := by
    calc
      _ = 1 / ‖d‖ := by rw [norm_inv, one_div]
      _ ≤ 2 / ‖D‖ := (div_le_div_iff₀ hdp hDp).mpr (by nlinarith)
      _ = 2 * ‖D⁻¹‖ := by rw [norm_inv, div_eq_mul_inv]
      _ ≤ 2 * L := mul_le_mul_of_nonneg_left hinv (by norm_num)
  refine ⟨hd, hactualInv, ?_⟩
  rw [norm_div]
  exact (div_le_iff₀ hdp).mpr (by nlinarith)

/-- The exact scalar Schur correction is stable under four entry errors,
with a constant depending only on reciprocal-pivot and cross-ratio bounds. -/
theorem scalar_minor_stability_from_ratios (a x y d A X Y D : ℂ) (K L δ : ℝ)
    (hD : D ≠ 0) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hinv : ‖D⁻¹‖ ≤ L) (hX : ‖X / D‖ ≤ K) (hY : ‖Y / D‖ ≤ K)
    (ha : ‖a - A‖ ≤ δ) (hx : ‖x - X‖ ≤ δ) (hy : ‖y - Y‖ ≤ δ)
    (hd : ‖d - D‖ ≤ δ) (hsmall : L * δ ≤ 1 / 2) :
    ‖(a - x * y / d) - (A - X * Y / D)‖ ≤ 2 * (K + 1) ^ 2 * δ := by
  have htransfer := scalar_pivot_transfer d D L δ hD hδ hinv hd hsmall
  have hactualRatio : ‖y / d‖ ≤ 2 * K + 1 := by
    have heq : y / d = (Y / D) * (D / d) + (y - Y) * d⁻¹ := by field_simp [hD, htransfer.1]
    rw [heq]
    calc
      _ ≤ ‖Y / D‖ * ‖D / d‖ + ‖y - Y‖ * ‖d⁻¹‖ := by
        simpa only [norm_mul] using norm_add_le ((Y / D) * (D / d)) ((y - Y) * d⁻¹)
      _ ≤ K * 2 + δ * (2 * L) := add_le_add
        (mul_le_mul hY htransfer.2.2 (norm_nonneg _) hK)
        (mul_le_mul hy htransfer.2.1 (norm_nonneg _) hδ)
      _ ≤ 2 * K + 1 := by nlinarith
  have hidentity : (a - x * y / d) - (A - X * Y / D) = (a - A) -
      ((x - X) * (y / d) + (X / D) * (D / d) * (y - Y) +
        (X / D) * (Y / D) * (D / d) * (D - d)) := by
    field_simp [hD, htransfer.1]
    ring
  have h1 : ‖(x - X) * (y / d)‖ ≤ δ * (2 * K + 1) := by
    rw [norm_mul]
    exact mul_le_mul hx hactualRatio (norm_nonneg _) hδ
  have h2 : ‖(X / D) * (D / d) * (y - Y)‖ ≤ K * 2 * δ := by
    simp only [norm_mul]
    exact mul_le_mul (mul_le_mul hX htransfer.2.2 (norm_nonneg _) hK) hy (norm_nonneg _) (by positivity)
  have h3 : ‖(X / D) * (Y / D) * (D / d) * (D - d)‖ ≤ K * K * 2 * δ := by
    simp only [norm_mul]
    have hd' : ‖D - d‖ ≤ δ := by simpa only [norm_sub_rev] using hd
    apply mul_le_mul _ hd' (norm_nonneg _) (by positivity)
    exact mul_le_mul (mul_le_mul hX hY (norm_nonneg _) hK) htransfer.2.2 (norm_nonneg _) (by positivity)
  rw [hidentity]
  have hsum := (norm_add_le ((x - X) * (y / d) + (X / D) * (D / d) * (y - Y))
    ((X / D) * (Y / D) * (D / d) * (D - d))).trans
      (add_le_add_right (norm_add_le _ _) _)
  have hh := norm_sub_le (a - A)
    ((x - X) * (y / d) + (X / D) * (D / d) * (y - Y) + (X / D) * (Y / D) * (D / d) * (D - d))
  nlinarith

end LocalLaw
