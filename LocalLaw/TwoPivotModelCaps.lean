import LocalLaw.SelectedFirstPairOccupancy
import LocalLaw.ModelCompletionSchur

/-! # Uniform genuine deleted-model caps for at most two pivots

A block close to the nonzero scalar p has bounded inverse row sums. The
actual Schur deletion identity then bounds the correctly deficient deleted
kernel. In particular no additional finite reference class for a model with
two deleted sampled vertices is postulated.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance twoPivotCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section ScalarBlock
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem two_pivot_inverse_rows (A : Matrix I I ℂ) (hA : IsUnit A)
    (p : ℂ) (hp : p≠0) (P δ : ℝ) (hP : 0≤P) (hδ : 0≤δ)
    (hpinv : ‖p⁻¹‖≤P) (hcard : Fintype.card I≤2)
    (herror : ∀ i j,‖(A-p•1) i j‖≤δ) (hsmall : 2*P*δ≤1/2) :
    (∀ i,∑ j,‖A⁻¹ i j‖≤2*P) ∧ (∀ j,∑ i,‖A⁻¹ i j‖≤2*P) := by
  let D : Matrix I I ℂ := Matrix.diagonal (fun _=>p)
  let U : Matrix I I ℂ := Matrix.diagonal (fun _=>p⁻¹)
  have hD : IsUnit D := Matrix.isUnit_diagonal.mpr
    (Pi.isUnit_iff.mpr (fun _=>isUnit_iff_ne_zero.mpr hp))
  have hDU : D*U=1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [mul_inv_cancel₀ hp,Matrix.diagonal_one]
  have hDinv : D⁻¹=U := Matrix.inv_eq_right_inv hDU
  have hrow : ∀ i,∑ j,‖D⁻¹ i j‖≤P := by
    intro i
    rw [hDinv]
    simpa [U,Matrix.diagonal_apply,apply_ite] using hpinv
  have hcol : ∀ j,∑ i,‖D⁻¹ i j‖≤P := by
    intro j
    rw [hDinv]
    simpa [U,Matrix.diagonal_apply,apply_ite] using hpinv
  have hdim : (Fintype.card I:ℝ)≤2 := by exact_mod_cast hcard
  have hsmall' : (Fintype.card I:ℝ)*P*δ≤1/2 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdim hP) hδ).trans hsmall
  apply inverse_row_column_stability A D hA hD P δ hP hδ hrow hcol
    (fun i j=>?_) hsmall'
  simpa only [D,Matrix.smul_one_eq_diagonal] using herror i j

end ScalarBlock

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

/-- The actual kernel after deleting at most two vertices, with all units
derived from the dissipative extension matrix and scalar-block proximity. -/
theorem two_pivot_deleted_kernel_bound (g : DeficientGraph V d) (hd : 3≤d)
    (T : Set V) (hcard : Nat.card T≤2) (q z p : ℂ) (hz : 0<z.im) (hq : 0≤q.im)
    (hp : p≠0) (C P δ : ℝ) (hC : 0≤C) (hP : 0≤P) (hδ : 0≤δ)
    (hkernel : ∀ i j,‖g.extensionGreen q z i j‖≤C) (hpinv : ‖p⁻¹‖≤P)
    (herror : ∀ i j:T,‖((g.extensionGreen q z).submatrix
      (Subtype.val:T→V) (Subtype.val:T→V)-p•1) i j‖≤δ)
    (hsmall : 2*P*δ≤1/2) (i j : (Tᶜ:Set V)) :
    ‖(g.delete T).extensionGreen q z i j‖≤C+4*P*C^2 := by
  let K:=g.extensionGreen q z
  let A:=K.submatrix (Subtype.val:T→V) (Subtype.val:T→V)
  let X:=K.submatrix (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)
  let Y:=K.submatrix (Subtype.val:T→V) (Subtype.val:(Tᶜ:Set V)→V)
  have hunit:=g.extensionMatrix_isUnit hd q z hz hq
  have hdeleted: IsUnit ((g.extensionMatrix q z).submatrix
      (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:(Tᶜ:Set V)→V)) := by
    rw [←g.extensionMatrix_delete T q z]
    exact (g.delete T).extensionMatrix_isUnit hd q z hz hq
  have hA:IsUnit A:=retained_principal_inverse_isUnit T (g.extensionMatrix q z) hunit hdeleted
  have hcard' : Fintype.card T≤2 := by simpa only [Nat.card_eq_fintype_card] using hcard
  have hrows:=two_pivot_inverse_rows A hA p hp P δ hP hδ hpinv hcard' herror hsmall
  have hAY : ∀ k:T,‖(A⁻¹*Y) k j‖≤(2*P)*C := fun k=>
    rectangular_product_row_bound A⁻¹ Y k j (2*P) C hC (hrows.1 k) (fun l=>hkernel l.val j.val)
  have hXrow : (∑ k:T,‖X i k‖)≤2*C := by
    calc
      _≤∑ _k:T,C := Finset.sum_le_sum (fun k _=>hkernel i.val k.val)
      _=(Fintype.card T:ℝ)*C := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _≤2*C := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard') hC
  have hprod : ‖(X*A⁻¹*Y) i j‖≤4*P*C^2 := by
    rw [Matrix.mul_assoc]
    have hh:=rectangular_product_row_bound X (A⁻¹*Y) i j (2*C) ((2*P)*C)
      (by positivity) hXrow hAY
    convert hh using 1
    ring
  rw [g.extensionGreen_delete hd T q z hz hq]
  exact (norm_sub_le _ _).trans ((add_le_add (hkernel i.val j.val) hprod))

end DeficientGraph
end LocalLaw
