import LocalLaw.FiniteRankSurgery
import LocalLaw.BoundarySupportedDeletion

/-!
# Sparse endpoint rows improve the surgery error

The global finite-rank comparison is strengthened on rows whose old error
has small sum and whose first-order forcing sees only small cross entries.
The resulting squared-error term suffices for the generalized source row
argument without reproducing the sharper cubic estimate in (5.52).
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance localSurgeryStabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem matrix_product_local_row_sum_bound (A E : Matrix I I ℂ) (i : I) (M e : ℝ)
    (he : 0 ≤ e) (hA : ∑ k, ‖A i k‖ ≤ M)
    (hE : ∀ k, A i k ≠ 0 → ∑ l, ‖E k l‖ ≤ e) :
    ∑ l, ‖(A * E) i l‖ ≤ M * e := by
  calc
    _ ≤ ∑ l, ∑ k, ‖A i k‖ * ‖E k l‖ :=
      Finset.sum_le_sum (fun l _ => matrix_mul_entry_norm_le A E i l)
    _ = ∑ k, ‖A i k‖ * (∑ l, ‖E k l‖) := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
    _ ≤ ∑ k, ‖A i k‖ * e := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : A i k = 0
      · simp only [hk, norm_zero, zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left (hE k hk) (norm_nonneg _)
    _ = (∑ k, ‖A i k‖) * e := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hA he

/-- Local old-error sums give an actual squared-error surgery improvement.
All final Green errors are conclusions of the two resolvent equations. -/
theorem surgery_local_entry_stability (R T P Q W : Matrix I I ℂ)
    (hT : T + R * W * T = R) (hQ : Q + Q * W * P = P)
    (C w δ e φ : ℝ) (hC : 0 ≤ C) (hw : 0 ≤ w) (hδ : 0 ≤ δ) (he : 0 ≤ e) (hφ : 0 ≤ φ)
    (hQrow : ∀ i, ∑ j, ‖Q i j‖ ≤ C) (hQcol : ∀ j, ∑ i, ‖Q i j‖ ≤ C)
    (hWrow : ∀ i, ∑ j, ‖W i j‖ ≤ w) (hWcol : ∀ j, ∑ i, ‖W i j‖ ≤ w)
    (hE : ∀ i j, ‖(R - P) i j‖ ≤ δ)
    (hsmall : (Fintype.card I : ℝ) * (1 + C * w) * w * δ ≤ 1 / 2)
    (i j : I)
    (hlocal : ∀ k, (1 - Q * W) i k ≠ 0 → ∑ l, ‖(R - P) k l‖ ≤ e)
    (hcross : ∀ k l, (1 - Q * W) i k ≠ 0 → (1 - W * Q) l j ≠ 0 → ‖(R - P) k l‖ ≤ φ) :
    ‖(T - Q) i j‖ ≤ (1 + C * w) ^ 2 * φ + 2 * (1 + C * w) ^ 3 * e * w * δ := by
  let A : Matrix I I ℂ := 1 - Q * W
  let B : Matrix I I ℂ := 1 - W * Q
  let E := R - P
  let F := T - Q
  let M := 1 + C * w
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hA : ∑ k, ‖A i k‖ ≤ M := by
    have hprod := matrix_product_row_sum_bound Q W C w hw hQrow hWrow i
    calc
      _ ≤ ∑ k, (‖(1 : Matrix I I ℂ) i k‖ + ‖(Q * W) i k‖) :=
        Finset.sum_le_sum (fun k _ => norm_sub_le _ _)
      _ = 1 + ∑ k, ‖(Q * W) i k‖ := by simp [Finset.sum_add_distrib, Matrix.one_apply, apply_ite norm]
      _ ≤ M := add_le_add_left hprod 1
  have hB : ∑ l, ‖B l j‖ ≤ M := by
    have hprod := matrix_product_row_sum_bound Q.transpose W.transpose C w hw hQcol hWcol j
    rw [← Matrix.transpose_mul] at hprod
    calc
      _ ≤ ∑ l, (‖(1 : Matrix I I ℂ) l j‖ + ‖(W * Q) l j‖) :=
        Finset.sum_le_sum (fun l _ => norm_sub_le _ _)
      _ = 1 + ∑ l, ‖(W * Q) l j‖ := by simp [Finset.sum_add_distrib, Matrix.one_apply, apply_ite norm]
      _ ≤ M := add_le_add_left hprod 1
  have hAE : ∑ l, ‖(A * E) i l‖ ≤ M * e :=
    matrix_product_local_row_sum_bound A E i M e he hA hlocal
  have hglobal : ∀ k l, ‖F k l‖ ≤ 2 * M ^ 2 * δ := fun k l =>
    surgery_entry_stability R T P Q W hT hQ C w δ hC hw hδ hQrow hQcol hWrow hWcol hE hsmall k l
  have hWF : ∀ k, ‖(W * F) k j‖ ≤ w * (2 * M ^ 2 * δ) := fun k =>
    matrix_mul_entry_bound_of_row W F k j w _ (by positivity) (hWrow k) (fun l => hglobal l j)
  have hprop : ‖(A * E * W * F) i j‖ ≤ 2 * M ^ 3 * e * w * δ := by
    rw [Matrix.mul_assoc (A * E) W F]
    have hh := matrix_mul_entry_bound_of_row (A * E) (W * F) i j (M * e) _ (by positivity) hAE hWF
    exact hh.trans_eq (by ring)
  have hforcing : ‖(A * E * B) i j‖ ≤ M ^ 2 * φ := by
    have hh := sandwich_entry_bound_of_support A E B i j φ M hφ hM hA hB hcross
    exact hh.trans_eq (by ring)
  have hid := congrArg (fun X : Matrix I I ℂ => X i j)
    (surgery_comparison_equation R T P Q W hT hQ)
  change F i j + (A * E * W * F) i j = (A * E * B) i j at hid
  have heq : F i j = (A * E * B) i j - (A * E * W * F) i j := (eq_sub_iff_add_eq).mpr hid
  change ‖F i j‖ ≤ _
  rw [heq]
  exact (norm_sub_le _ _).trans (add_le_add hforcing hprop)

end LocalLaw
