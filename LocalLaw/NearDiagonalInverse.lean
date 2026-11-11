import LocalLaw.FiniteRankSurgery

/-! # Genuine inverse rows for a finite block close to its own diagonal -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance nearDiagonalInverseDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {I : Type} [Fintype I] [DecidableEq I]

theorem inverse_rows_of_small_offdiagonal (A : Matrix I I ℂ) (hA : IsUnit A) (P e : ℝ)
    (hP : 0 ≤ P) (_he : 0 ≤ e) (hdiag : ∀ i, A i i ≠ 0)
    (hpivot : ∀ i, ‖(A i i)⁻¹‖ ≤ P)
    (hoff : ∀ i, ∑ j, ‖(A - Matrix.diagonal (fun k => A k k)) i j‖ ≤ e)
    (hsmall : P * e ≤ 1 / 2) : ∀ i, ∑ j, ‖A⁻¹ i j‖ ≤ 2 * P := by
  let D := Matrix.diagonal (fun i => A i i)
  let U := Matrix.diagonal (fun i => (A i i)⁻¹)
  let E := A - D
  have hDU : D * U = 1 := by
    rw [show D * U = Matrix.diagonal (fun i => A i i * (A i i)⁻¹) from Matrix.diagonal_mul_diagonal _ _]
    simp only [mul_inv_cancel₀ (hdiag _), Matrix.diagonal_one]
  have hBA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hidentity : A⁻¹ = U - A⁻¹ * (E * U) := by
    have hh : A⁻¹ * (E * U) = U - A⁻¹ := by
      dsimp only [E]
      rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, hBA, Matrix.one_mul, Matrix.mul_assoc, hDU, Matrix.mul_one]
    rw [hh]
    abel
  have hU : ∀ i, ∑ j, ‖U i j‖ ≤ P := by
    intro i
    have hh : (∑ j, ‖U i j‖) = ‖(A i i)⁻¹‖ := by
      calc
        _ = ∑ j, if j = i then ‖(A i i)⁻¹‖ else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : j = i
          · subst j; simp [U]
          · simp [U, Matrix.diagonal_apply, hj, Ne.symm hj]
        _ = _ := by simp
    rw [hh]
    exact hpivot i
  have hEU : ∀ i, ∑ j, ‖(E * U) i j‖ ≤ e * P :=
    matrix_product_row_sum_bound E U e P hP hoff hU
  intro i
  let R := ∑ j, ‖A⁻¹ i j‖
  have hprod : (∑ j, ‖(A⁻¹ * (E * U)) i j‖) ≤ R * (e * P) := by
    calc
      _ ≤ ∑ j, ∑ k, ‖A⁻¹ i k‖ * ‖(E * U) k j‖ :=
        Finset.sum_le_sum (fun j _ => matrix_mul_entry_norm_le _ _ i j)
      _ = ∑ k, ‖A⁻¹ i k‖ * (∑ j, ‖(E * U) k j‖) := by rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]
      _ ≤ ∑ k, ‖A⁻¹ i k‖ * (e * P) :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hEU k) (norm_nonneg _))
      _ = _ := (Finset.sum_mul ..).symm
  have hrow : R ≤ P + R * (e * P) := by
    calc
      _ = ∑ j, ‖(U - A⁻¹ * (E * U)) i j‖ := by rw [← hidentity]
      _ ≤ ∑ j, (‖U i j‖ + ‖(A⁻¹ * (E * U)) i j‖) := Finset.sum_le_sum (fun _ _ => norm_sub_le _ _)
      _ = (∑ j, ‖U i j‖) + ∑ j, ‖(A⁻¹ * (E * U)) i j‖ := Finset.sum_add_distrib
      _ ≤ _ := add_le_add (hU i) hprod
  have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hsmall hR]

theorem inverse_entry_difference_own_diagonal (A : Matrix I I ℂ) (hA : IsUnit A) (P δ : ℝ)
    (hP : 0 ≤ P) (hδ : 0 ≤ δ) (hdiag : ∀ i, A i i ≠ 0)
    (hpivot : ∀ i, ‖(A i i)⁻¹‖ ≤ P)
    (hoff : ∀ i j, i ≠ j → ‖A i j‖ ≤ δ)
    (small : (Fintype.card I : ℝ) * P * δ ≤ 1 / 2) (i j : I) :
    ‖(A⁻¹ - Matrix.diagonal (fun k => (A k k)⁻¹)) i j‖ ≤ 2 * P ^ 2 * δ := by
  let D := Matrix.diagonal (fun k => A k k)
  have hD : IsUnit D := Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr
    (fun k => isUnit_iff_ne_zero.mpr (hdiag k)))
  let U := Matrix.diagonal (fun k => (A k k)⁻¹)
  have hDU : D * U = 1 := by
    rw [show D * U = Matrix.diagonal (fun k => A k k * (A k k)⁻¹) from Matrix.diagonal_mul_diagonal _ _]
    simp only [mul_inv_cancel₀ (hdiag _), Matrix.diagonal_one]
  have hDinv : D⁻¹ = U := Matrix.inv_eq_right_inv hDU
  have hsum : D + (A - D) = A := by abel
  have hPW : IsUnit (D + (A - D)) := hsum.symm ▸ hA
  have hrow : ∀ k, ∑ l, ‖D⁻¹ k l‖ ≤ P := by
    intro k
    rw [hDinv]
    have hh : (∑ l, ‖U k l‖) = ‖(A k k)⁻¹‖ := by
      calc
        _ = ∑ l, if l = k then ‖(A k k)⁻¹‖ else 0 := by
          apply Finset.sum_congr rfl
          intro l _
          by_cases hkl : l = k
          · subst l; simp [U]
          · simp [U, Matrix.diagonal_apply, hkl, Ne.symm hkl]
        _ = _ := by simp
    rw [hh]
    exact hpivot k
  have hcol : ∀ l, ∑ k, ‖D⁻¹ k l‖ ≤ P := by
    intro l
    have hh := hrow l
    rw [hDinv] at hh ⊢
    have heq : (∑ k, ‖U k l‖) = ∑ k, ‖U l k‖ := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hkl : k = l
      · subst k; rfl
      · simp [U, Matrix.diagonal_apply, hkl, Ne.symm hkl]
    rw [heq]
    exact hh
  have hE : ∀ k l, ‖(A - D) k l‖ ≤ δ := by
    intro k l
    by_cases hkl : k = l
    · subst l
      simpa [D] using hδ
    · simpa only [D, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hkl, sub_zero] using hoff k l hkl
  have hh := inverse_entry_stability D (A - D) hD hPW P δ hP hδ hrow hcol hE small i j
  simpa only [hsum, hDinv, U] using hh

end LocalLaw
