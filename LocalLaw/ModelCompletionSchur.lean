import LocalLaw.DeficientBoundaryGram
import LocalLaw.BoundarySchurRows
import LocalLaw.FiniteRankSurgery

/-! # Exact finite-model completion across an arbitrary restriction

The completion error is the genuine deleted-ghost Green block minus qI,
projected through the literal cut incidence. It is not silently zero.
All full, deleted and retained inverse units are derived for Im(z)>0,
Im(q)>=0, without a reference class for the completed graph.
-/

noncomputable section
namespace LocalLaw
local instance completionSchurDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V:Type}[Fintype V][DecidableEq V]{d:ℕ}

def modelCompletionBoundaryDefect (g:DeficientGraph V d)(T:Set V)(q z:ℂ) :
    Matrix (BoundaryOrientedEdge g.graph T) (BoundaryOrientedEdge g.graph T) ℂ :=
  ((g.delete T).extensionGreen q z).submatrix (boundaryOutsideVertex g.graph T)
    (boundaryOutsideVertex g.graph T)-q•1

theorem model_completion_inverse_difference (g:DeficientGraph V d)(hd:3≤d)
    (T:Set V)(q z:ℂ)(hz:0<z.im)(hq:0≤q.im) :
    let R:=(g.extensionGreen q z).submatrix (Subtype.val:T→V) (Subtype.val:T→V)
    let P:=(g.restrict T).extensionGreen q z
    let U:=cutInnerCoupling g.graph d T
    IsUnit R ∧ IsUnit P ∧ P⁻¹-R⁻¹=U*g.modelCompletionBoundaryDefect T q z*U.transpose := by
  dsimp only
  have hM:=g.extensionMatrix_isUnit hd q z hz hq
  have hD:IsUnit ((g.extensionMatrix q z).submatrix (Subtype.val:(Tᶜ:Set V)→V)
      (Subtype.val:(Tᶜ:Set V)→V)) := by
    rw [←g.extensionMatrix_delete T q z]
    exact (g.delete T).extensionMatrix_isUnit hd q z hz hq
  have hR:=retained_principal_inverse_isUnit T (g.extensionMatrix q z) hM hD
  have hSchur:=retained_principal_inverse T (g.extensionMatrix q z) hM hD
  rw [g.extensionMatrix_retained_block hd T q z,g.extensionMatrix_cross12 T q z,
    g.extensionMatrix_cross21 T q z,←g.extensionMatrix_delete T q z] at hSchur
  have hSelf:=normalized_cut_selfEnergy g.graph d T ((g.delete T).extensionGreen q z)
  change (g.H.submatrix (Subtype.val:T→V) (Subtype.val:(Tᶜ:Set V)→V))*
    (g.delete T).extensionGreen q z*(g.H.submatrix (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V))=_ at hSelf
  change ((g.extensionGreen q z).submatrix (Subtype.val:T→V) (Subtype.val:T→V))⁻¹=
    (g.restrict T).extensionMatrix q z+q•(cutInnerCoupling g.graph d T*(cutInnerCoupling g.graph d T).transpose)-
      g.H.submatrix (Subtype.val:T→V) (Subtype.val:(Tᶜ:Set V)→V)*
        (g.delete T).extensionGreen q z*g.H.submatrix (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V) at hSchur
  rw [hSelf] at hSchur
  have hPM:=(g.restrict T).extensionMatrix_isUnit hd q z hz hq
  have hP:IsUnit ((g.restrict T).extensionGreen q z) := Matrix.isUnit_nonsing_inv_iff.mpr hPM
  have hPinv:((g.restrict T).extensionGreen q z)⁻¹=(g.restrict T).extensionMatrix q z :=
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hPM)
  refine ⟨hR,hP,?_⟩
  rw [hPinv,hSchur]
  unfold modelCompletionBoundaryDefect
  rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one]
  abel

/-- Exact completed-minus-restricted kernel identity. -/
theorem model_completion_difference (g:DeficientGraph V d)(hd:3≤d)
    (T:Set V)(q z:ℂ)(hz:0<z.im)(hq:0≤q.im) :
    let R:=(g.extensionGreen q z).submatrix (Subtype.val:T→V) (Subtype.val:T→V)
    let P:=(g.restrict T).extensionGreen q z
    let U:=cutInnerCoupling g.graph d T
    R-P=(R*U)*g.modelCompletionBoundaryDefect T q z*(U.transpose*P) := by
  dsimp only
  let R:=(g.extensionGreen q z).submatrix (Subtype.val:T→V) (Subtype.val:T→V)
  let P:=(g.restrict T).extensionGreen q z
  let U:=cutInnerCoupling g.graph d T
  have h:=g.model_completion_inverse_difference hd T q z hz hq
  have hR:=Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).mp h.1)
  have hP:=Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp h.2.1)
  have hid:R*(P⁻¹-R⁻¹)*P=R-P := by
    rw [Matrix.mul_sub,Matrix.sub_mul]
    calc
      _=R*(P⁻¹*P)-(R*R⁻¹)*P := by simp only [Matrix.mul_assoc]
      _=R-P := by rw [hR,hP,Matrix.mul_one,Matrix.one_mul]
  change R-P=(R*U)*g.modelCompletionBoundaryDefect T q z*(U.transpose*P)
  rw [←hid,h.2.2]
  simp only [Matrix.mul_assoc]
  rfl

/-- Exact vacuum completion requires only a vanishing projected defect;
no entrywise identity for repeated boundary labels is incorrectly imposed. -/
theorem model_completion_eq_of_projected_defect_zero (g:DeficientGraph V d)(hd:3≤d)
    (T:Set V)(q z:ℂ)(hz:0<z.im)(hq:0≤q.im)
    (hzero:cutInnerCoupling g.graph d T*g.modelCompletionBoundaryDefect T q z*
      (cutInnerCoupling g.graph d T).transpose=0) :
    (g.extensionGreen q z).submatrix (Subtype.val:T→V) (Subtype.val:T→V)=
      (g.restrict T).extensionGreen q z := by
  apply sub_eq_zero.mp
  rw [g.model_completion_difference hd T q z hz hq]
  calc
    _=(g.extensionGreen q z).submatrix (Subtype.val:T→V) (Subtype.val:T→V)*
        (cutInnerCoupling g.graph d T*g.modelCompletionBoundaryDefect T q z*
          (cutInnerCoupling g.graph d T).transpose)*(g.restrict T).extensionGreen q z := by
      simp only [Matrix.mul_assoc]
    _=0 := by rw [hzero,Matrix.mul_zero,Matrix.zero_mul]

end DeficientGraph
end LocalLaw
