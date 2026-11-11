import LocalLaw.DiagonalKernelStability
import LocalLaw.CavityTreeFeedback

/-!
# Finite Schur localization from ordinary and exceptional boundary terms

The ordinary diagonal error is absorbed through the actual kernel equation.
The exceptional coupling is estimated by its genuine entry mass and decay
from both target vertices. This is the analytic split used after classifying
the actual deleted components in the localization principle.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem sandwich_entry_norm_le_mass (P W Q : Matrix V V ℂ) (J : Finset V)
    (hsupport : ∀ a b, W a b ≠ 0 → a ∈ J ∧ b ∈ J)
    (i j : V) (A B : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hP : ∀ a ∈ J, ‖P i a‖ ≤ A) (hQ : ∀ b ∈ J, ‖Q b j‖ ≤ B) :
    ‖(P * W * Q) i j‖ ≤ (A * B) * (∑ a, ∑ b, ‖W a b‖) := by
  calc
    _ ≤ ∑ b, ∑ a, ‖P i a‖ * ‖W a b‖ * ‖Q b j‖ := by
      change ‖∑ b, (P * W) i b * Q b j‖ ≤ _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b _
      rw [Matrix.mul_apply, Finset.sum_mul]
      simpa only [norm_mul] using norm_sum_le Finset.univ (fun a => (P i a * W a b) * Q b j)
    _ ≤ ∑ b, ∑ a, (A * B) * ‖W a b‖ := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro a _
      by_cases hw : W a b = 0
      · simp only [hw, norm_zero, mul_zero, zero_mul, le_refl]
      · have hab := hsupport a b hw
        have hp := mul_le_mul_of_nonneg_right (hP a hab.1) (norm_nonneg (W a b))
        exact (mul_le_mul hp (hQ b hab.2) (norm_nonneg _) (mul_nonneg hA (norm_nonneg _))).trans_eq (by ring)
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]

/-- A diagonal ordinary self-energy plus a finite exceptional coupling
gives the localization error. Neither a desired inverse difference nor an
assumed scalar feedback inequality is an input to this theorem. -/
theorem schur_localization_split_bound (A W : Matrix V V ℂ) (e : V → ℂ)
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
    (i j : V) (ρ Cfull M : ℝ) (hρ : 0 ≤ ρ) (hCfull : 0 ≤ Cfull)
    (hnear : ∀ a ∈ J, K i a ≤ ρ)
    (hfullcol : ∀ b ∈ J, ‖(A - Matrix.diagonal e - W)⁻¹ b j‖ ≤ Cfull * ρ)
    (hmass : (∑ a, ∑ b, ‖W a b‖) ≤ M) :
    ‖A⁻¹ i j - (A - Matrix.diagonal e - W)⁻¹ i j‖ ≤
      2 * τ * C ^ 2 * C₀ * B i j + 2 * C * Cfull * ρ ^ 2 * M := by
  let T := A - Matrix.diagonal e
  have hstable := complex_diagonal_kernel_stability A e hA hordinary d τ hτ he K B C C₀ Ddiam
    hd hK hB hC hC₀ hDdiam reference companion convolution small
  have hPg : ∀ a ∈ J, ‖T⁻¹ i a‖ ≤ 2 * C * ρ := by
    intro a ha
    exact (hstable i a).2.trans (mul_le_mul_of_nonneg_left (hnear a ha) (by positivity))
  have hbad := sandwich_entry_norm_le_mass T⁻¹ W (T - W)⁻¹ J hsupport i j
    (2 * C * ρ) (Cfull * ρ) (by positivity) (mul_nonneg hCfull hρ) hPg hfullcol
  have hid : T⁻¹ - (T - W)⁻¹ = -(T⁻¹ * W * (T - W)⁻¹) := by
    rw [matrix_inverse_difference T (T - W) hordinary hfull]
    noncomm_ring
  have hbadentry := congrArg (fun P : Matrix V V ℂ => P i j) hid
  change T⁻¹ i j - (T - W)⁻¹ i j = -(T⁻¹ * W * (T - W)⁻¹) i j at hbadentry
  have hbadnorm : ‖T⁻¹ i j - (T - W)⁻¹ i j‖ ≤ 2 * C * Cfull * ρ ^ 2 * M := by
    rw [hbadentry, norm_neg]
    apply hbad.trans
    have hh := mul_le_mul_of_nonneg_left hmass
      (mul_nonneg (by positivity : 0 ≤ 2 * C * ρ) (mul_nonneg hCfull hρ))
    convert hh using 1; ring
  have hdiag : ‖A⁻¹ i j - T⁻¹ i j‖ ≤ 2 * τ * C ^ 2 * C₀ * B i j := by
    simpa only [Matrix.sub_apply, norm_sub_rev] using (hstable i j).1
  have hsplit : A⁻¹ i j - (T - W)⁻¹ i j = (A⁻¹ i j - T⁻¹ i j) +
      (T⁻¹ i j - (T - W)⁻¹ i j) := by ring
  change ‖A⁻¹ i j - (T - W)⁻¹ i j‖ ≤ _
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hdiag hbadnorm)

end LocalLaw
