import LocalLaw.FiniteRankSurgeryColumns

/-!
# Surgery error columns restricted to actual sampled tips

The filtered old left-error column is distinct from a full endpoint error
column. Central unsampled endpoints need not have small absolute column
sums. An already established uniform new error controls the remaining
nonlinear term.
-/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance filteredSurgeryColumnsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]

omit [DecidableEq I] in
theorem matrix_product_mapped_column_sum_bound (A B : Matrix I I ℂ) (tip : J→I)
    (s r : ℝ) (hs : 0≤s) (hA : ∀ k, ∑ a:J, ‖A (tip a) k‖≤s)
    (j : I) (hB : ∑ k, ‖B k j‖≤r) :
    (∑ a:J, ‖(A*B) (tip a) j‖)≤s*r := by
  calc
    _ ≤ ∑ a:J, ∑ k, ‖A (tip a) k‖*‖B k j‖ :=
      Finset.sum_le_sum (fun a _ => matrix_mul_entry_norm_le A B (tip a) j)
    _ = ∑ k, (∑ a:J, ‖A (tip a) k‖)*‖B k j‖ := by rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
    _ ≤ ∑ k, s*‖B k j‖ := Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hA k) (norm_nonneg _))
    _ = s*∑ k, ‖B k j‖ := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hB hs

/-- The exact comparison equation propagates a filtered old error column;
no bound on unsampled central error column sums is assumed. -/
theorem filtered_surgery_column_bound (R T P Q W : Matrix I I ℂ)
    (hT : T+R*W*T=R) (hQ : Q+Q*W*P=P) (tip : J→I)
    (C w s Γ : ℝ) (_hC : 0≤C) (hw : 0≤w) (hs : 0≤s) (hΓ : 0≤Γ)
    (hQcol : ∀ k, ∑ i, ‖Q i k‖≤C)
    (hWcol : ∀ k, ∑ i, ‖W i k‖≤w) (hWrow : ∀ i, ∑ k, ‖W i k‖≤w)
    (hleft : ∀ k, ∑ a:J, ‖((1-Q*W)*(R-P)) (tip a) k‖≤s)
    (hglobal : ∀ i k, ‖(T-Q) i k‖≤Γ) (j : I) :
    (∑ a:J, ‖(T-Q) (tip a) j‖)≤s*(1+C*w+(Fintype.card I:ℝ)*w*Γ) := by
  let A : Matrix I I ℂ := 1-Q*W
  let B : Matrix I I ℂ := 1-W*Q
  let E := R-P
  let F := T-Q
  let M := 1+C*w
  have hB : ∑ i, ‖B i j‖≤M := by
    have hp := matrix_product_single_column_sum_bound W Q w C hw hWcol j (hQcol j)
    calc
      _ ≤ ∑ i, (‖(1:Matrix I I ℂ) i j‖+‖(W*Q) i j‖) := Finset.sum_le_sum (fun i _ => norm_sub_le _ _)
      _ = 1+∑ i, ‖(W*Q) i j‖ := by simp [Finset.sum_add_distrib,Matrix.one_apply,apply_ite norm]
      _ ≤ 1+w*C := add_le_add_left hp _
      _ = M := by dsimp only [M]; ring
  have hWF (i : I) : ‖(W*F) i j‖≤w*Γ :=
    matrix_mul_entry_bound_of_row W F i j w Γ hΓ (hWrow i) (fun k => hglobal k j)
  have hWFsum : ∑ i, ‖(W*F) i j‖≤(Fintype.card I:ℝ)*w*Γ := by
    exact (Finset.sum_le_sum (fun i _ => hWF i)).trans_eq (by simp; ring)
  have hforce : (∑ a:J, ‖(A*E*B) (tip a) j‖)≤s*M :=
    matrix_product_mapped_column_sum_bound (A*E) B tip s M hs hleft j hB
  have hrem : (∑ a:J, ‖(A*E*W*F) (tip a) j‖)≤s*((Fintype.card I:ℝ)*w*Γ) := by
    rw [Matrix.mul_assoc (A*E) W F]
    exact matrix_product_mapped_column_sum_bound (A*E) (W*F) tip s _ hs hleft j hWFsum
  have hid := surgery_comparison_equation R T P Q W hT hQ
  have heq : F=A*E*B-A*E*W*F := by
    change F+A*E*W*F=A*E*B at hid
    exact (eq_sub_iff_add_eq).mpr hid
  calc
    _ = ∑ a:J, ‖(A*E*B-A*E*W*F) (tip a) j‖ := by rw [←heq]
    _ ≤ ∑ a:J, (‖(A*E*B) (tip a) j‖+‖(A*E*W*F) (tip a) j‖) := Finset.sum_le_sum (fun a _ => norm_sub_le _ _)
    _ = _ := Finset.sum_add_distrib
    _ ≤ s*M+s*((Fintype.card I:ℝ)*w*Γ) := add_le_add hforce hrem
    _ = _ := by dsimp only [M]; ring

end LocalLaw
