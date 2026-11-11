import LocalLaw.WeightedWoodburyTarget
import LocalLaw.BoundaryResolvent

/-! # Square rows through supported inverse surgery

The estimate depends on a target's endpoint weight, not the number of
sampled edges. This supplies boundary-parameter continuity without a
reference-class assumption for the switched model.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance supportedSquareRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V I J : Type*} [Fintype V] [Fintype I]

theorem rectangular_product_square_row_bound (A : Matrix J I ℂ) (B : Matrix I V ℂ)
    (a S : ℝ) (_ha : 0≤a) (hS : 0≤S) (x : J)
    (hA : ∑ i,‖A x i‖≤a) (hB : ∀ i,∑ k,‖B i k‖^2≤S) :
    (∑ k,‖(A*B) x k‖^2)≤a^2*S := by
  have hprod (i j : I) : (∑ k,‖B i k‖*‖B j k‖)≤S :=
    boundary_product_sum_le (fun k=>B i k) (fun k=>B j k) S (hB i) (hB j)
  have heq (k : V) : (∑ i,‖A x i‖*‖B i k‖)^2=
      ∑ i,∑ j,(‖A x i‖*‖A x j‖)*(‖B i k‖*‖B j k‖) := by
    rw [pow_two,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    _ ≤ ∑ k,(∑ i,‖A x i‖*‖B i k‖)^2 := by
      apply Finset.sum_le_sum
      intro k _
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [Matrix.mul_apply,norm_mul] using norm_sum_le Finset.univ (fun i=>A x i*B i k)
    _ = ∑ i,∑ j,(‖A x i‖*‖A x j‖)*(∑ k,‖B i k‖*‖B j k‖) := by
      simp_rw [heq]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ i,∑ j,(‖A x i‖*‖A x j‖)*S := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (hprod i j) (by positivity))
    _ = (∑ i,‖A x i‖)^2*S := by
      rw [pow_two,Finset.sum_mul_sum,Finset.sum_mul]
      simp only [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hA 2) hS

theorem rectangular_product_target_row_sum (A : Matrix J I ℂ) (B : Matrix I I ℂ)
    (a w : ℝ) (hw : 0≤w) (x : J) (hA : ∑ i,‖A x i‖≤a)
    (hB : ∀ i,∑ j,‖B i j‖≤w) : (∑ j,‖(A*B) x j‖)≤a*w := by
  calc
    _≤∑ j,∑ i,‖A x i‖*‖B i j‖ := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [Matrix.mul_apply,norm_mul] using norm_sum_le Finset.univ (fun i=>A x i*B i j)
    _=∑ i,‖A x i‖*(∑ j,‖B i j‖) := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _≤∑ i,‖A x i‖*w := Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (hB i) (norm_nonneg _))
    _=(∑ i,‖A x i‖)*w := (Finset.sum_mul ..).symm
    _≤a*w := mul_le_mul_of_nonneg_right hA hw

variable [DecidableEq V]

theorem inverse_supported_square_row (A B : Matrix V V ℂ) (hA : IsUnit A) (hB : IsUnit B)
    (e : I↪V) (hsupport : ∀ u v,u∉Set.range e ∨ v∉Set.range e→(B-A) u v=0)
    (a w S : ℝ) (ha : 0≤a) (hw : 0≤w) (hS : 0≤S) (x : V)
    (hOld : ∀ v,∑ k,‖A⁻¹ v k‖^2≤S)
    (hNewEndpoints : ∑ i,‖B⁻¹ x (e i)‖≤a)
    (hW : ∀ i,∑ j,‖(B-A) (e i) (e j)‖≤w) :
    (∑ k,‖B⁻¹ x k‖^2)≤2*(1+(a*w)^2)*S := by
  let X:=B⁻¹.submatrix id e
  let W:=(B-A).submatrix e e
  let Y:=A⁻¹.submatrix e id
  have hcoeff:∑ i,‖(X*W) x i‖≤a*w :=
    rectangular_product_target_row_sum X W a w hw x hNewEndpoints hW
  have hprod:∑ k,‖(X*W*Y) x k‖^2≤(a*w)^2*S :=
    rectangular_product_square_row_bound (X*W) Y (a*w) S (mul_nonneg ha hw) hS x hcoeff (fun i=>hOld (e i))
  have hh: A⁻¹-B⁻¹=B⁻¹*(B-A)*A⁻¹ := by
    have hr:=Matrix.inv_sub_inv (show IsUnit B↔IsUnit A from ⟨fun _=>hA,fun _=>hB⟩)
    rw [show A-B= -(B-A) by abel,Matrix.mul_neg,Matrix.neg_mul] at hr
    simpa only [neg_sub,neg_neg] using congrArg Neg.neg hr
  rw [supported_single_middle_product e B⁻¹ (B-A) A⁻¹ hsupport] at hh
  have hpoint (k : V): ‖B⁻¹ x k‖^2≤2*‖A⁻¹ x k‖^2+2*‖(X*W*Y) x k‖^2 := by
    have he:=congrArg (fun M : Matrix V V ℂ=>M x k) hh
    change A⁻¹ x k-B⁻¹ x k=(X*W*Y) x k at he
    have hnorm:=norm_sub_le (A⁻¹ x k) ((X*W*Y) x k)
    have hv:B⁻¹ x k=A⁻¹ x k-(X*W*Y) x k := by rw [←he]; ring
    rw [←hv] at hnorm
    nlinarith [sq_nonneg (‖A⁻¹ x k‖-‖(X*W*Y) x k‖),norm_nonneg (B⁻¹ x k)]
  calc
    _≤∑ k,(2*‖A⁻¹ x k‖^2+2*‖(X*W*Y) x k‖^2) := Finset.sum_le_sum (fun k _=>hpoint k)
    _=2*(∑ k,‖A⁻¹ x k‖^2)+2*(∑ k,‖(X*W*Y) x k‖^2) := by
      rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
    _≤2*S+2*((a*w)^2*S) := by linarith [hOld x]
    _=_ := by ring

end LocalLaw
