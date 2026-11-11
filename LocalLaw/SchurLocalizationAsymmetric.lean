import LocalLaw.SchurLocalizationEstimate

/-! # Localization with separate distances from the two targets -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem schur_localization_split_bound_asymmetric (A W : Matrix V V ℂ) (e : V → ℂ)
    (hA : IsUnit A) (hordinary : IsUnit (A - Matrix.diagonal e))
    (hfull : IsUnit (A - Matrix.diagonal e - W))
    (d : V → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (he : ∀ v, ‖e v‖ ≤ τ * d v)
    (K B : V → V → ℝ) (C C₀ Ddiam : ℝ)
    (hd : ∀ k, 0 ≤ d k) (hK : ∀ i j, 0 ≤ K i j) (hB : ∀ i j, 0 < B i j)
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hDdiam : 0 ≤ Ddiam)
    (reference : ∀ i j, ‖A⁻¹ i j‖ ≤ C * K i j)
    (companion : ∀ i j, B i j ≤ Ddiam * K i j)
    (convolution : ∀ i j, (∑ k, d k * K i k * K k j) ≤ C₀ * B i j)
    (small : τ * C * C₀ * Ddiam ≤ 1 / 2)
    (J : Finset V) (hsupport : ∀ a b, W a b ≠ 0 → a ∈ J ∧ b ∈ J)
    (i j : V) (ρi ρj Cfull M : ℝ) (hρi : 0 ≤ ρi) (hρj : 0 ≤ ρj) (hCfull : 0 ≤ Cfull)
    (hnear : ∀ a ∈ J, K i a ≤ ρi)
    (hfullcol : ∀ b ∈ J, ‖(A - Matrix.diagonal e - W)⁻¹ b j‖ ≤ Cfull * ρj)
    (hmass : (∑ a, ∑ b, ‖W a b‖) ≤ M) :
    ‖A⁻¹ i j - (A - Matrix.diagonal e - W)⁻¹ i j‖ ≤
      2 * τ * C ^ 2 * C₀ * B i j + 2 * C * Cfull * (ρi * ρj) * M := by
  let T := A - Matrix.diagonal e
  have hstable := complex_diagonal_kernel_stability A e hA hordinary d τ hτ he K B C C₀ Ddiam
    hd hK hB hC hC₀ hDdiam reference companion convolution small
  have hPg : ∀ a ∈ J, ‖T⁻¹ i a‖ ≤ 2 * C * ρi := by
    intro a ha
    exact (hstable i a).2.trans (mul_le_mul_of_nonneg_left (hnear a ha) (by positivity))
  have hbad := sandwich_entry_norm_le_mass T⁻¹ W (T - W)⁻¹ J hsupport i j
    (2 * C * ρi) (Cfull * ρj) (by positivity) (mul_nonneg hCfull hρj) hPg hfullcol
  have hid : T⁻¹ - (T - W)⁻¹ = -(T⁻¹ * W * (T - W)⁻¹) := by
    rw [matrix_inverse_difference T (T - W) hordinary hfull]
    noncomm_ring
  have hbadentry := congrArg (fun P : Matrix V V ℂ => P i j) hid
  change T⁻¹ i j - (T - W)⁻¹ i j = -(T⁻¹ * W * (T - W)⁻¹) i j at hbadentry
  have hbadnorm : ‖T⁻¹ i j - (T - W)⁻¹ i j‖ ≤ 2 * C * Cfull * (ρi * ρj) * M := by
    rw [hbadentry, norm_neg]
    apply hbad.trans
    have hh := mul_le_mul_of_nonneg_left hmass
      (mul_nonneg (by positivity : 0 ≤ 2 * C * ρi) (mul_nonneg hCfull hρj))
    convert hh using 1; ring
  have hdiag : ‖A⁻¹ i j - T⁻¹ i j‖ ≤ 2 * τ * C ^ 2 * C₀ * B i j := by
    simpa only [Matrix.sub_apply, norm_sub_rev] using (hstable i j).1
  have hsplit : A⁻¹ i j - (T - W)⁻¹ i j = (A⁻¹ i j - T⁻¹ i j) +
      (T⁻¹ i j - (T - W)⁻¹ i j) := by ring
  change ‖A⁻¹ i j - (T - W)⁻¹ i j‖ ≤ _
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hdiag hbadnorm)

end LocalLaw
