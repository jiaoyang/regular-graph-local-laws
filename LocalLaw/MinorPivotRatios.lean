import LocalLaw.MinorIdentity
import LocalLaw.DeletionStability

/-!
# Reference pivot ratios from the genuine deleted inverse

The inverse of the deleted matrix controls normalized full inverse entries
and the reciprocal full diagonal. This avoids assuming a uniform cap on the
full reference matrix in the singleton comparison.
-/

open scoped BigOperators
namespace LocalLaw
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_deleted_add_at {E : Type*} [AddCommMonoid E] (b : V) (f : V → E) :
    (∑ k : {k : V // k ≠ b}, f k.val) + f b = ∑ k : V, f k := by
  classical
  have hh : (∑ k : {k : V // k ≠ b}, f k.val) = ∑ k ∈ Finset.univ.erase b, f k :=
    (Finset.sum_subtype (Finset.univ.erase b) (by simp [ne_comm]) f).symm
  rw [hh]
  exact Finset.sum_erase_add _ _ (Finset.mem_univ _)

/-- Exact normalized inverse column in terms of the actual deleted inverse. -/
theorem inverse_deleted_column_ratio (A P : Matrix V V ℂ) (b : V)
    (hleft : P * A = 1) (hpivot : P b b ≠ 0) (i : {i : V // i ≠ b}) :
    P i.val b / P b b = -∑ k : {k : V // k ≠ b},
      (A.submatrix (Subtype.val : {i : V // i ≠ b} → V) (Subtype.val : {i : V // i ≠ b} → V))⁻¹ i k * A k.val b := by
  classical
  rw [deleted_matrix_inverse A P b hleft hpivot]
  let f := fun k : V => (P i.val k - P i.val b * P b k / P b b) * A k b
  have hb : f b = 0 := by dsimp [f]; simp [hpivot]
  change P i.val b / P b b = -∑ k : {k : V // k ≠ b}, f k.val
  rw [sum_deleted_eq_sum_of_zero b f hb]
  dsimp only [f]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  have hfactor : (∑ k : V, (P i.val b * P b k / P b b) * A k b) =
      (P i.val b / P b b) * ∑ k : V, P b k * A k b := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hfactor]
  change P i.val b / P b b = -((P * A) i.val b - (P i.val b / P b b) * (P * A) b b)
  rw [hleft]
  simp only [Matrix.one_apply, if_neg i.property, if_pos rfl, ite_true, mul_one, zero_sub, neg_neg]

/-- The reciprocal full pivot is its original diagonal plus the normalized
cross-column coupling, obtained from the actual right inverse equation. -/
theorem inverse_pivot_identity (A P : Matrix V V ℂ) (b : V)
    (hright : A * P = 1) (hpivot : P b b ≠ 0) :
    (P b b)⁻¹ = A b b + ∑ k : {k : V // k ≠ b}, A b k.val * (P k.val b / P b b) := by
  have hsum := sum_deleted_add_at b (fun k : V => A b k * (P k b / P b b))
  have hfull : (∑ k : V, A b k * (P k b / P b b)) = (P b b)⁻¹ := by
    calc
      _ = (A * P) b b / P b b := by
        rw [Matrix.mul_apply, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [hright]; simp only [Matrix.one_apply, if_pos rfl, ite_true, one_div]
  rw [hfull, div_self hpivot, mul_one] at hsum
  exact hsum.symm.trans (add_comm _ _)

/-- A bounded deleted kernel and a coupling-column sum bound the full pivot
ratio, independently of the magnitude of the full inverse entries. -/
theorem inverse_deleted_column_ratio_bound (A P : Matrix V V ℂ) (b : V)
    (hleft : P * A = 1) (hpivot : P b b ≠ 0) (C M : ℝ) (hC : 0 ≤ C)
    (hkernel : ∀ i k : {i : V // i ≠ b},
      ‖(A.submatrix (Subtype.val : {i : V // i ≠ b} → V) (Subtype.val : {i : V // i ≠ b} → V))⁻¹ i k‖ ≤ C)
    (hcoupling : (∑ k : {k : V // k ≠ b}, ‖A k.val b‖) ≤ M) (i : {i : V // i ≠ b}) :
    ‖P i.val b / P b b‖ ≤ C * M := by
  rw [inverse_deleted_column_ratio A P b hleft hpivot i, norm_neg]
  calc
    _ ≤ ∑ k : {k : V // k ≠ b},
      ‖(A.submatrix (Subtype.val : {i : V // i ≠ b} → V) (Subtype.val : {i : V // i ≠ b} → V))⁻¹ i k‖ * ‖A k.val b‖ := by
        simpa only [norm_mul] using norm_sum_le Finset.univ
          (fun k : {k : V // k ≠ b} =>
            (A.submatrix (Subtype.val : {i : V // i ≠ b} → V) (Subtype.val : {i : V // i ≠ b} → V))⁻¹ i k * A k.val b)
    _ ≤ ∑ k : {k : V // k ≠ b}, C * ‖A k.val b‖ :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hkernel i k) (norm_nonneg _))
    _ = C * ∑ k : {k : V // k ≠ b}, ‖A k.val b‖ := (Finset.mul_sum ..).symm
    _ ≤ C * M := mul_le_mul_of_nonneg_left hcoupling hC

theorem inverse_pivot_norm_bound (A P : Matrix V V ℂ) (b : V)
    (hright : A * P = 1) (hpivot : P b b ≠ 0) (B M K : ℝ) (hK : 0 ≤ K)
    (hdiag : ‖A b b‖ ≤ B) (hrow : (∑ k : {k : V // k ≠ b}, ‖A b k.val‖) ≤ M)
    (hratio : ∀ k : {k : V // k ≠ b}, ‖P k.val b / P b b‖ ≤ K) :
    ‖(P b b)⁻¹‖ ≤ B + M * K := by
  rw [inverse_pivot_identity A P b hright hpivot]
  calc
    _ ≤ ‖A b b‖ + ‖∑ k : {k : V // k ≠ b}, A b k.val * (P k.val b / P b b)‖ := norm_add_le _ _
    _ ≤ B + ∑ k : {k : V // k ≠ b}, ‖A b k.val‖ * ‖P k.val b / P b b‖ :=
      add_le_add hdiag (by
        simpa only [norm_mul] using norm_sum_le Finset.univ
          (fun k : {k : V // k ≠ b} => A b k.val * (P k.val b / P b b)))
    _ ≤ B + ∑ k : {k : V // k ≠ b}, ‖A b k.val‖ * K :=
      add_le_add_left (Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hratio k) (norm_nonneg _))) _
    _ = B + (∑ k : {k : V // k ≠ b}, ‖A b k.val‖) * K := by rw [Finset.sum_mul]
    _ ≤ B + M * K := add_le_add_left (mul_le_mul_of_nonneg_right hrow hK) _

end LocalLaw
