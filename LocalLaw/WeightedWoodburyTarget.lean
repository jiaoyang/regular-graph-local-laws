import LocalLaw.PhysicalMinorSurgery
import LocalLaw.FiniteRankSurgery
import LocalLaw.DeletionStability

/-! # Target-specific Woodbury stability without a support-cardinality loss -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance weightedWoodburyTargetDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V I J K : Type*} [Fintype V] [Fintype I] [DecidableEq V]

theorem matrix_mul_of_left_columns_supported (e : I↪V) (A : Matrix J V ℂ) (B : Matrix V K ℂ)
    (hA : ∀ i v,v∉Set.range e→A i v=0) :
    A*B=A.submatrix id e*B.submatrix e id := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.submatrix_apply,id_eq]
  apply sum_embedding_of_supported e
  intro v hv
  rw [hA i v hv,zero_mul]

theorem matrix_mul_of_right_rows_supported (e : I↪V) (A : Matrix J V ℂ) (B : Matrix V K ℂ)
    (hB : ∀ v j,v∉Set.range e→B v j=0) :
    A*B=A.submatrix id e*B.submatrix e id := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.submatrix_apply,id_eq]
  apply sum_embedding_of_supported e
  intro v hv
  rw [hB v j hv,mul_zero]

theorem supported_double_middle_product (e : I↪V) (A D B C : Matrix V V ℂ)
    (hD : ∀ x y,x∉Set.range e ∨ y∉Set.range e→D x y=0) :
    A*D*B*D*C=A.submatrix id e*D.submatrix e e*B.submatrix e e*
      D.submatrix e e*C.submatrix e id := by
  let X:=A.submatrix id e
  let Y:=C.submatrix e id
  let R:=D.submatrix e id
  let W:=D.submatrix e e
  let Q:=B.submatrix e e
  have hAD : A*D=X*R := matrix_mul_of_right_rows_supported e A D (fun v j hv=>hD v j (Or.inl hv))
  have hRB : R*B=W*B.submatrix e id := by
    exact matrix_mul_of_left_columns_supported e R B (fun i v hv=>hD (e i) v (Or.inr hv))
  have hRBsub : (R*B).submatrix id e=W*Q := by
    rw [hRB]
    ext i j
    rfl
  have hRBD : R*B*D=(W*Q)*R := by
    have hh:=matrix_mul_of_right_rows_supported e (R*B) D (fun v j hv=>hD v j (Or.inl hv))
    rw [hRBsub] at hh
    exact hh
  have hRC : R*C=W*Y :=
    matrix_mul_of_left_columns_supported e R C (fun i v hv=>hD (e i) v (Or.inr hv))
  change A*D*B*D*C=X*W*Q*W*Y
  rw [hAD]
  calc
    _=X*(R*B*D)*C := by simp only [Matrix.mul_assoc]
    _=X*((W*Q)*R)*C := by rw [hRBD]
    _=(X*W*Q)*(R*C) := by simp only [Matrix.mul_assoc]
    _=_ := by rw [hRC]; simp only [Matrix.mul_assoc]

theorem inverse_second_order_identity (A B : Matrix V V ℂ) (hA : IsUnit A) (hB : IsUnit B) :
    B⁻¹=A⁻¹-A⁻¹*(B-A)*A⁻¹+A⁻¹*(B-A)*B⁻¹*(B-A)*A⁻¹ := by
  have hleft : A⁻¹-B⁻¹=A⁻¹*(B-A)*B⁻¹ := by
    rw [Matrix.inv_sub_inv (show IsUnit A↔IsUnit B from ⟨fun _=>hB,fun _=>hA⟩)]
  have hright : A⁻¹-B⁻¹=B⁻¹*(B-A)*A⁻¹ := by
    have hh:=Matrix.inv_sub_inv (show IsUnit B↔IsUnit A from ⟨fun _=>hA,fun _=>hB⟩)
    rw [show A-B= -(B-A) by abel,Matrix.mul_neg,Matrix.neg_mul] at hh
    simpa only [neg_sub,neg_neg] using congrArg Neg.neg hh
  have hh:=congrArg (fun X : Matrix V V ℂ=>A⁻¹*(B-A)*X) hright
  dsimp only at hh
  have he : A⁻¹*(B-A)*A⁻¹-A⁻¹*(B-A)*B⁻¹=
      A⁻¹*(B-A)*B⁻¹*(B-A)*A⁻¹ := by
    calc
      _=A⁻¹*(B-A)*(A⁻¹-B⁻¹) := (Matrix.mul_sub (A⁻¹*(B-A)) A⁻¹ B⁻¹).symm
      _=A⁻¹*(B-A)*(B⁻¹*(B-A)*A⁻¹) := hh
      _=_ := by simp only [Matrix.mul_assoc]
  have hfirst : B⁻¹=A⁻¹-A⁻¹*(B-A)*B⁻¹ := by
    apply eq_sub_iff_add_eq.mpr
    rw [←hleft]
    abel
  calc
    _=A⁻¹-A⁻¹*(B-A)*B⁻¹ := hfirst
    _=_ := by rw [←he]; abel

theorem supported_single_middle_product (e : I↪V) (A D C : Matrix V V ℂ)
    (hD : ∀ x y,x∉Set.range e ∨ y∉Set.range e→D x y=0) :
    A*D*C=A.submatrix id e*D.submatrix e e*C.submatrix e id := by
  have hAD := matrix_mul_of_right_rows_supported e A D (fun v j hv=>hD v j (Or.inl hv))
  have hDC := matrix_mul_of_left_columns_supported e (D.submatrix e id) C
    (fun i v hv=>hD (e i) v (Or.inr hv))
  rw [hAD,Matrix.mul_assoc,hDC]
  simp only [Matrix.mul_assoc]
  rfl

/-- Replace the actual updated endpoint block in the exact second-order
inverse identity. The target weights remain literal old inverse entries. -/
def woodburyTargetMatrix (A : Matrix V V ℂ) (e : I↪V) (W Q : Matrix I I ℂ) : Matrix V V ℂ :=
  A⁻¹-A⁻¹.submatrix id e*W*A⁻¹.submatrix e id+
    A⁻¹.submatrix id e*W*Q*W*A⁻¹.submatrix e id

theorem inverse_eq_woodburyTargetMatrix (A B : Matrix V V ℂ) (hA : IsUnit A) (hB : IsUnit B)
    (e : I↪V) (hsupport : ∀ x y,x∉Set.range e ∨ y∉Set.range e→(B-A) x y=0) :
    B⁻¹=woodburyTargetMatrix A e ((B-A).submatrix e e) (B⁻¹.submatrix e e) := by
  calc
    _=A⁻¹-A⁻¹*(B-A)*A⁻¹+A⁻¹*(B-A)*B⁻¹*(B-A)*A⁻¹ := inverse_second_order_identity A B hA hB
    _=_ := by
      rw [supported_single_middle_product e A⁻¹ (B-A) A⁻¹ hsupport,
        supported_double_middle_product e A⁻¹ (B-A) B⁻¹ A⁻¹ hsupport]
      rfl


theorem woodburyTargetMatrix_difference_bound (A : Matrix V V ℂ) (e : I↪V)
    (W P Q : Matrix I I ℂ) (w a b σ : ℝ) (hw : 0≤w) (_ha : 0≤a) (_hb : 0≤b) (hσ : 0≤σ)
    (hWrow : ∀ i,∑ j,‖W i j‖≤w) (hWcol : ∀ j,∑ i,‖W i j‖≤w)
    (herror : ∀ i j,‖P i j-Q i j‖≤σ) (x y : V)
    (hleft : ∑ i,‖A⁻¹ x (e i)‖≤a) (hright : ∑ i,‖A⁻¹ (e i) y‖≤b) :
    ‖woodburyTargetMatrix A e W P x y-woodburyTargetMatrix A e W Q x y‖≤w^2*a*b*σ := by
  let X:=A⁻¹.submatrix id e
  let Y:=A⁻¹.submatrix e id
  let E:=P-Q
  have hEW (i j : I) : ‖(E*W) i j‖≤σ*w :=
    matrix_mul_entry_bound_of_column E W i j σ w hσ (fun k=>herror i k) (hWcol j)
  have hWEW (i j : I) : ‖(W*E*W) i j‖≤w^2*σ := by
    rw [Matrix.mul_assoc]
    exact (matrix_mul_entry_bound_of_row W (E*W) i j w (σ*w) (by positivity)
      (hWrow i) (fun k=>hEW k j)).trans_eq (by ring)
  have hXWEW (j : I) : ‖(X*(W*E*W)) x j‖≤a*(w^2*σ) :=
    rectangular_product_row_bound X (W*E*W) x j a (w^2*σ) (by positivity) hleft (fun k=>hWEW k j)
  have hprod := rectangular_product_column_bound (X*(W*E*W)) Y x y (a*(w^2*σ)) b
    (by positivity) hXWEW hright
  have hid : woodburyTargetMatrix A e W P-woodburyTargetMatrix A e W Q=X*(W*E*W)*Y := by
    dsimp only [woodburyTargetMatrix,X,Y,E]
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  have hentry := congrArg (fun M : Matrix V V ℂ=>M x y) hid
  change woodburyTargetMatrix A e W P x y-woodburyTargetMatrix A e W Q x y=_ at hentry
  rw [hentry]
  exact hprod.trans_eq (by ring)

theorem inverse_woodbury_target_stability (A B : Matrix V V ℂ) (hA : IsUnit A) (hB : IsUnit B)
    (e : I↪V) (hsupport : ∀ x y,x∉Set.range e ∨ y∉Set.range e→(B-A) x y=0)
    (Q : Matrix I I ℂ) (w a b σ : ℝ) (hw : 0≤w) (ha : 0≤a) (hb : 0≤b) (hσ : 0≤σ)
    (hWrow : ∀ i,∑ j,‖(B-A) (e i) (e j)‖≤w)
    (hWcol : ∀ j,∑ i,‖(B-A) (e i) (e j)‖≤w)
    (herror : ∀ i j,‖B⁻¹ (e i) (e j)-Q i j‖≤σ) (x y : V)
    (hleft : ∑ i,‖A⁻¹ x (e i)‖≤a) (hright : ∑ i,‖A⁻¹ (e i) y‖≤b) :
    ‖B⁻¹ x y-woodburyTargetMatrix A e ((B-A).submatrix e e) Q x y‖≤w^2*a*b*σ := by
  have hh:=woodburyTargetMatrix_difference_bound A e ((B-A).submatrix e e)
    (B⁻¹.submatrix e e) Q w a b σ hw ha hb hσ hWrow hWcol herror x y hleft hright
  rw [←inverse_eq_woodburyTargetMatrix A B hA hB e hsupport] at hh
  exact hh

end LocalLaw
