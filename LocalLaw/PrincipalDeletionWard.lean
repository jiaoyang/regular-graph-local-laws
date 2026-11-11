import LocalLaw.CavityAveragePerturbation
import LocalLaw.PrincipalDeletion

/-!
# Ward bounds for an actual principal deletion

The Schur correction uses the true removed Green block. Averaging its absolute
entries costs the L1 norm of that block's inverse and one Ward factor, rather
than a pointwise inverse-imaginary-part estimate for every Green factor.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance principalWardDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Extend the physical deleted Green matrix by the original entries when
at least one index is removed. Only retained entries are used physically. -/
def maskedDeletedGreen (H : Matrix V V ℂ) (T : Set V) (z : ℂ) : Matrix V V ℂ :=
  fun i j => if hi : i ∉ T then if hj : j ∉ T then
    green (H.submatrix (Subtype.val : (Tᶜ : Set V) → V)
      (Subtype.val : (Tᶜ : Set V) → V)) z ⟨i, hi⟩ ⟨j, hj⟩
    else green H z i j else green H z i j

def principalSchurCorrection (H : Matrix V V ℂ) (T : Set V) (z : ℂ) : Matrix V V ℂ :=
  (green H z).submatrix id (Subtype.val : T → V) *
    ((green H z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ *
      (green H z).submatrix (Subtype.val : T → V) id

theorem maskedDeletedGreen_difference_bound (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (T : Set V) (z : ℂ) (hz : 0 < z.im) (i j : V) :
    ‖green H z i j - maskedDeletedGreen H T z i j‖ ≤ ‖principalSchurCorrection H T z i j‖ := by
  by_cases hi : i ∉ T
  · by_cases hj : j ∉ T
    · simp only [maskedDeletedGreen, dif_pos hi, dif_pos hj]
      have hh := congrArg (fun M : Matrix (Tᶜ : Set V) (Tᶜ : Set V) ℂ => M ⟨i, hi⟩ ⟨j, hj⟩)
        (green_deleted_principal T H hH z hz)
      change green (H.submatrix (Subtype.val : (Tᶜ : Set V) → V)
        (Subtype.val : (Tᶜ : Set V) → V)) z ⟨i, hi⟩ ⟨j, hj⟩ =
          green H z i j - principalSchurCorrection H T z i j at hh
      rw [hh, sub_sub_cancel]
    · simpa only [maskedDeletedGreen, dif_pos hi, dif_neg hj, sub_self, norm_zero] using
        norm_nonneg (principalSchurCorrection H T z i j)
  · simpa only [maskedDeletedGreen, dif_neg hi, sub_self, norm_zero] using
      norm_nonneg (principalSchurCorrection H T z i j)

theorem weighted_principalSchurCorrection_ward (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (T : Set V) (z : ℂ) (hz : 0 < z.im)
    (W : Matrix V V ℝ) (D I : ℝ) (hW : ∀ i j, 0 ≤ W i j) (hD : 0 ≤ D)
    (hrow : ∀ i, ∑ j, W i j = D) (hcol : ∀ j, ∑ i, W i j = D)
    (hI : ∀ u, (green H z u u).im ≤ I) :
    (∑ i, ∑ j, W i j * ‖principalSchurCorrection H T z i j‖) ≤
      (D * I / z.im) * (∑ u : T, ∑ v : T,
        ‖((green H z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ u v‖) := by
  let A := ((green H z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹
  have hentry : ∀ i j, ‖principalSchurCorrection H T z i j‖ ≤
      ∑ u : T, ∑ v : T, ‖green H z i u.val‖ * ‖A u v‖ * ‖green H z v.val j‖ := by
    intro i j
    unfold principalSchurCorrection
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro u _
    rw [norm_mul, Matrix.mul_apply]
    calc
      _ ≤ ‖green H z i u.val‖ * ∑ v : T, ‖A u v * green H z v.val j‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
      _ = _ := by simp_rw [Finset.mul_sum, norm_mul, mul_assoc]
  calc
    _ ≤ ∑ i, ∑ j, W i j * (∑ u : T, ∑ v : T,
        ‖green H z i u.val‖ * ‖A u v‖ * ‖green H z v.val j‖) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hentry i j) (hW i j)
    _ = ∑ u : T, ∑ v : T, ‖A u v‖ *
        (∑ i, ∑ j, W i j * ‖green H z i u.val‖ * ‖green H z v.val j‖) := by
      simp_rw [Finset.mul_sum]
      conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ u : T, ∑ v : T, ‖A u v‖ * (D * I / z.im) := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro v _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (weighted_green_product_ward H H hH hH z hz W D hW hrow hcol u.val v.val).trans
      apply (div_le_iff₀ (by positivity : 0 < 2 * z.im)).mpr
      calc
        _ ≤ D * (I + I) := mul_le_mul_of_nonneg_left (add_le_add (hI u.val) (hI v.val)) hD
        _ = _ := by field_simp; ring
    _ = _ := by simp_rw [← Finset.sum_mul]; ring

/-- A physical principal deletion has a weighted L1 comparison even though
the two physical resolvents have different index types. -/
theorem weighted_maskedDeletedGreen_difference_ward (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (T : Set V) (z : ℂ) (hz : 0 < z.im)
    (W : Matrix V V ℝ) (D I : ℝ) (hW : ∀ i j, 0 ≤ W i j) (hD : 0 ≤ D)
    (hrow : ∀ i, ∑ j, W i j = D) (hcol : ∀ j, ∑ i, W i j = D)
    (hI : ∀ u, (green H z u u).im ≤ I) :
    (∑ i, ∑ j, W i j * ‖green H z i j - maskedDeletedGreen H T z i j‖) ≤
      (D * I / z.im) * (∑ u : T, ∑ v : T,
        ‖((green H z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ u v‖) := by
  apply le_trans _ (weighted_principalSchurCorrection_ward H hH T z hz W D I hW hD hrow hcol hI)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (maskedDeletedGreen_difference_bound H hH T z hz i j) (hW i j)

end
end LocalLaw
