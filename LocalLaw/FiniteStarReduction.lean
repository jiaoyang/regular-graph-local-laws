import LocalLaw.BlockSchur
import LocalLaw.WeightedWoodburyTarget

/-! # Exact finite-star reduction with different ambient core sizes

Only the retained core Green block and the supported sampled couplings
enter the reduced matrix. Its unit and its exact inverse principal block
follow from the upper-core Schur complement. No sampled-block unit is used.
-/

noncomputable section
set_option maxHeartbeats 2000000
namespace LocalLaw
local instance finiteStarDecidable (p : Prop) : Decidable p := Classical.propDecidable p

private theorem finiteStar_inverse_upper {V J : Type} [Fintype V] [Fintype J]
    [DecidableEq V] [DecidableEq J] (A : Matrix V V ℂ) (U : Matrix V J ℂ)
    (Vt : Matrix J V ℂ) (D : Matrix J J ℂ) (hA : IsUnit A)
    (hM : IsUnit (Matrix.fromBlocks A U Vt D)) :
    (Matrix.fromBlocks A U Vt D)⁻¹=
      Matrix.fromBlocks (A⁻¹+A⁻¹*U*(D-Vt*A⁻¹*U)⁻¹*Vt*A⁻¹)
        (-(A⁻¹*U*(D-Vt*A⁻¹*U)⁻¹)) (-((D-Vt*A⁻¹*U)⁻¹*Vt*A⁻¹))
        (D-Vt*A⁻¹*U)⁻¹ := by
  letI : Invertible A:=Classical.choice hA.nonempty_invertible
  have hC : IsUnit (D-Vt*⅟ A*U) := by
    simpa only [Matrix.invOf_eq_nonsing_inv] using
      (inverse_block22 (Matrix.fromBlocks A U Vt D) hM hA).1
  letI : Invertible (D-Vt*⅟ A*U):=Classical.choice hC.nonempty_invertible
  letI := Matrix.fromBlocks₁₁Invertible A U Vt D
  simpa only [Matrix.invOf_eq_nonsing_inv] using Matrix.invOf_fromBlocks₁₁_eq A U Vt D

private theorem finiteStar_blocks_submatrix {V I J : Type} (A : Matrix V V ℂ)
    (U : Matrix V J ℂ) (Vt : Matrix J V ℂ) (D : Matrix J J ℂ) (e : I→V) :
    (Matrix.fromBlocks A U Vt D).submatrix (Sum.map e id) (Sum.map e id)=
      Matrix.fromBlocks (A.submatrix e e) (U.submatrix e id) (Vt.submatrix id e) D := by
  ext x y
  cases x <;> cases y <;> rfl

def finiteStarMatrix {V I J : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (A : Matrix V V ℂ) (U : Matrix V J ℂ) (Vt : Matrix J V ℂ) (D : Matrix J J ℂ) (e : I↪V) :
    Matrix (I⊕J) (I⊕J) ℂ :=
  Matrix.fromBlocks (A⁻¹.submatrix e e)⁻¹ (U.submatrix e id) (Vt.submatrix id e) D

theorem finite_star_reduction {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    [DecidableEq V] [DecidableEq I] [DecidableEq J]
    (A : Matrix V V ℂ) (U : Matrix V J ℂ) (Vt : Matrix J V ℂ) (D : Matrix J J ℂ) (e : I↪V)
    (hA : IsUnit A) (hM : IsUnit (Matrix.fromBlocks A U Vt D))
    (hR : IsUnit (A⁻¹.submatrix e e))
    (hU : ∀v j,v∉Set.range e→U v j=0) (hV : ∀j v,v∉Set.range e→Vt j v=0) :
    IsUnit (finiteStarMatrix A U Vt D e) ∧
      (finiteStarMatrix A U Vt D e)⁻¹=
        (Matrix.fromBlocks A U Vt D)⁻¹.submatrix (Sum.map e id) (Sum.map e id) := by
  let R:=A⁻¹.submatrix e e
  let Ur:=U.submatrix e id
  let Vr:=Vt.submatrix id e
  let C:=D-Vt*A⁻¹*U
  let M:=Matrix.fromBlocks A U Vt D
  let S:=Matrix.fromBlocks R⁻¹ Ur Vr D
  have hRinv : IsUnit R⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hR
  have hRdouble : R⁻¹⁻¹=R := Matrix.nonsing_inv_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).mp hR)
  have hAUfull : A⁻¹*U=A⁻¹.submatrix id e*Ur :=
    matrix_mul_of_right_rows_supported e A⁻¹ U hU
  have hVAfull : Vt*A⁻¹=Vr*A⁻¹.submatrix e id :=
    matrix_mul_of_left_columns_supported e Vt A⁻¹ hV
  have hAU : (A⁻¹*U).submatrix e id=R*Ur := by rw [hAUfull];rfl
  have hVA : (Vt*A⁻¹).submatrix id e=Vr*R := by rw [hVAfull];rfl
  have hVAU : Vt*A⁻¹*U=Vr*R*Ur := by
    have hh:=matrix_mul_of_right_rows_supported e (Vt*A⁻¹) U hU
    rw [hVA] at hh
    exact hh
  have hC : IsUnit C := (inverse_block22 M hM hA).1
  have hSchur : D-Vr*R*Ur=C := by dsimp only [C];rw [hVAU]
  have hS : IsUnit S := by
    letI : Invertible R⁻¹:=Classical.choice hRinv.nonempty_invertible
    apply Matrix.isUnit_fromBlocks_iff_of_invertible₁₁.mpr
    simpa only [Matrix.invOf_eq_nonsing_inv,hRdouble,hSchur] using hC
  have hFm:=finiteStar_inverse_upper A U Vt D hA hM
  have hFs:=finiteStar_inverse_upper R⁻¹ Ur Vr D hRinv hS
  rw [hRdouble,hSchur] at hFs
  have hquad : (A⁻¹*U*C⁻¹*Vt*A⁻¹).submatrix e e=R*Ur*C⁻¹*Vr*R := by
    calc
      _=((A⁻¹*U)*C⁻¹*(Vt*A⁻¹)).submatrix e e := by simp only [Matrix.mul_assoc]
      _=(A⁻¹*U).submatrix e id*C⁻¹*(Vt*A⁻¹).submatrix id e := rfl
      _=R*Ur*C⁻¹*(Vr*R) := by rw [hAU,hVA]
      _=_ := by simp only [Matrix.mul_assoc]
  have hTL : (A⁻¹+A⁻¹*U*C⁻¹*Vt*A⁻¹).submatrix e e=R+R*Ur*C⁻¹*Vr*R := by
    change R+(A⁻¹*U*C⁻¹*Vt*A⁻¹).submatrix e e=R+R*Ur*C⁻¹*Vr*R
    rw [hquad]
  have hTR : (-(A⁻¹*U*C⁻¹)).submatrix e id=-(R*Ur*C⁻¹) := by
    change -((A⁻¹*U*C⁻¹).submatrix e id)=-(R*Ur*C⁻¹)
    have hh : (A⁻¹*U*C⁻¹).submatrix e id=(A⁻¹*U).submatrix e id*C⁻¹ := rfl
    rw [hh,hAU]
  have hBL : (-(C⁻¹*Vt*A⁻¹)).submatrix id e=-(C⁻¹*Vr*R) := by
    change -((C⁻¹*Vt*A⁻¹).submatrix id e)=-(C⁻¹*Vr*R)
    congr 1
    calc
      _=(C⁻¹*(Vt*A⁻¹)).submatrix id e := by simp only [Matrix.mul_assoc]
      _=C⁻¹*(Vt*A⁻¹).submatrix id e := rfl
      _=C⁻¹*(Vr*R) := by rw [hVA]
      _=_ := by simp only [Matrix.mul_assoc]
  refine ⟨hS,?_⟩
  change S⁻¹=M⁻¹.submatrix (Sum.map e id) (Sum.map e id)
  rw [hFs,hFm,finiteStar_blocks_submatrix]
  change Matrix.fromBlocks (R+R*Ur*C⁻¹*Vr*R) (-(R*Ur*C⁻¹)) (-(C⁻¹*Vr*R)) C⁻¹=
    Matrix.fromBlocks ((A⁻¹+A⁻¹*U*C⁻¹*Vt*A⁻¹).submatrix e e)
      ((-(A⁻¹*U*C⁻¹)).submatrix e id) ((-(C⁻¹*Vt*A⁻¹)).submatrix id e) C⁻¹
  rw [hTL,hTR,hBL]

end LocalLaw
