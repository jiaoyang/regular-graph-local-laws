import LocalLaw.FiniteRankSurgery

/-!
# Dimension-free column stability under finite surgery

An actual old error column bound propagates through the two exact update
identities. The contraction uses the column error itself, rather than the
number of surgery endpoints times a uniform entry error.
-/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance finiteRankSurgeryColumnsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem matrix_product_single_column_sum_bound (A B : Matrix I I ℂ) (r s : ℝ)
    (hr : 0≤r) (hA : ∀ k, ∑ i, ‖A i k‖≤r) (j : I) (hB : ∑ k, ‖B k j‖≤s) :
    ∑ i, ‖(A*B) i j‖≤r*s := by
  calc
    _ ≤ ∑ i, ∑ k, ‖A i k‖*‖B k j‖ := Finset.sum_le_sum (fun i _ => matrix_mul_entry_norm_le A B i j)
    _ = ∑ k, (∑ i, ‖A i k‖)*‖B k j‖ := by rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
    _ ≤ ∑ k, r*‖B k j‖ := Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hA k) (norm_nonneg _))
    _ = r*∑ k, ‖B k j‖ := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hB hr

/-- The exact surgery comparison propagates old column sums without a
surgery-dimension factor. The Green comparison remains a conclusion. -/
theorem surgery_column_stability (R T P Q W : Matrix I I ℂ)
    (hT : T+R*W*T=R) (hQ : Q+Q*W*P=P)
    (C w e : ℝ) (hC : 0≤C) (hw : 0≤w) (he : 0≤e)
    (hQcol : ∀ j, ∑ i, ‖Q i j‖≤C) (hWcol : ∀ j, ∑ i, ‖W i j‖≤w)
    (hEcol : ∀ j, ∑ i, ‖(R-P) i j‖≤e)
    (hsmall : (1+C*w)*e*w≤1/2) (j : I) :
    ∑ i, ‖(T-Q) i j‖≤2*(1+C*w)^2*e := by
  let A : Matrix I I ℂ := 1-Q*W
  let B : Matrix I I ℂ := 1-W*Q
  let E := R-P
  let F := T-Q
  let M := 1+C*w
  let Γ := ∑ i, ‖F i j‖
  have hM : 0≤M := by dsimp only [M]; positivity
  have hΓ : 0≤Γ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hA : ∀ k, ∑ i, ‖A i k‖≤M := by
    intro k
    have hp := matrix_product_single_column_sum_bound Q W C w hC hQcol k (hWcol k)
    calc
      _ ≤ ∑ i, (‖(1:Matrix I I ℂ) i k‖+‖(Q*W) i k‖) := Finset.sum_le_sum (fun i _ => norm_sub_le _ _)
      _ = 1+∑ i, ‖(Q*W) i k‖ := by simp [Finset.sum_add_distrib,Matrix.one_apply,apply_ite norm]
      _ ≤ M := add_le_add_left hp _
  have hB : ∀ k, ∑ i, ‖B i k‖≤M := by
    intro k
    have hp := matrix_product_single_column_sum_bound W Q w C hw hWcol k (hQcol k)
    calc
      _ ≤ ∑ i, (‖(1:Matrix I I ℂ) i k‖+‖(W*Q) i k‖) := Finset.sum_le_sum (fun i _ => norm_sub_le _ _)
      _ = 1+∑ i, ‖(W*Q) i k‖ := by simp [Finset.sum_add_distrib,Matrix.one_apply,apply_ite norm]
      _ ≤ 1+w*C := add_le_add_left hp _
      _ = M := by dsimp only [M]; ring
  have hAE : ∀ k, ∑ i, ‖(A*E) i k‖≤M*e := fun k =>
    matrix_product_single_column_sum_bound A E M e hM hA k (hEcol k)
  have hAEW : ∀ k, ∑ i, ‖(A*E*W) i k‖≤M*e*w := fun k =>
    matrix_product_single_column_sum_bound (A*E) W (M*e) w (mul_nonneg hM he) hAE k (hWcol k)
  have hrem : (∑ i, ‖(A*E*W*F) i j‖)≤M*e*w*Γ :=
    matrix_product_single_column_sum_bound (A*E*W) F (M*e*w) Γ (by positivity) hAEW j le_rfl
  have hforce : (∑ i, ‖(A*E*B) i j‖)≤M^2*e := by
    have hh := matrix_product_single_column_sum_bound (A*E) B (M*e) M (mul_nonneg hM he) hAE j (hB j)
    exact hh.trans_eq (by ring)
  have hid := surgery_comparison_equation R T P Q W hT hQ
  have heq : F=A*E*B-A*E*W*F := by
    change F+A*E*W*F=A*E*B at hid
    exact (eq_sub_iff_add_eq).mpr hid
  have hbound : Γ≤M^2*e+M*e*w*Γ := by
    calc
      _ = ∑ i, ‖(A*E*B-A*E*W*F) i j‖ := by rw [← heq]
      _ ≤ ∑ i, (‖(A*E*B) i j‖+‖(A*E*W*F) i j‖) := Finset.sum_le_sum (fun i _ => norm_sub_le _ _)
      _ = _ := Finset.sum_add_distrib
      _ ≤ _ := add_le_add hforce hrem
  have hcontract := mul_le_mul_of_nonneg_right hsmall hΓ
  change M*e*w*Γ≤1/2*Γ at hcontract
  have hhalf : Γ≤M^2*e+(1/2:ℝ)*Γ := hbound.trans (add_le_add_left hcontract _)
  have absorb (x y : ℝ) (h : x≤y+(1/2:ℝ)*x) : x≤2*y := by linarith
  exact (absorb Γ (M^2*e) hhalf).trans_eq (by dsimp only [M]; ring)

end LocalLaw
