import LocalLaw.PrincipalNearDiagonalRows

/-! # Transport indexed principal inverse rows to the literal removed set -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance embeddedPrincipalRowsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def embeddingImageSubsetEquiv (e:I↪V)(E:Set I) : E≃((e:I→V) '' E):=
  Equiv.ofBijective (fun i:E=>⟨e i.val,⟨i.val,i.property,rfl⟩⟩) (by
    constructor
    · intro i j h
      exact Subtype.ext (e.injective (congrArg Subtype.val h))
    · rintro ⟨v,i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩)

theorem embedded_principal_inverse_rows_cols (A:Matrix V V ℂ)(e:I↪V)(E:Set I)(C:ℝ)
    (hunit:IsUnit ((A.submatrix e e).submatrix (Subtype.val:E→I) (Subtype.val:E→I)))
    (hr:∀i:E,∑j:E,‖((A.submatrix e e).submatrix (Subtype.val:E→I) (Subtype.val:E→I))⁻¹ i j‖≤C)
    (hc:∀j:E,∑i:E,‖((A.submatrix e e).submatrix (Subtype.val:E→I) (Subtype.val:E→I))⁻¹ i j‖≤C) :
    let T:Set V:=(e:I→V) '' E
    let P:=A.submatrix (Subtype.val:T→V) (Subtype.val:T→V)
    IsUnit P ∧ (∀v:T,∑w:T,‖P⁻¹ v w‖≤C) ∧ (∀w:T,∑v:T,‖P⁻¹ v w‖≤C) := by
  dsimp only
  let T:Set V:=(e:I→V) '' E
  let P:=A.submatrix (Subtype.val:T→V) (Subtype.val:T→V)
  let U:=(A.submatrix e e).submatrix (Subtype.val:E→I) (Subtype.val:E→I)
  let φ:E≃T:=embeddingImageSubsetEquiv e E
  have hm:P.submatrix φ φ=U:=by ext i j;rfl
  have hu:IsUnit P:=(Matrix.isUnit_submatrix_equiv φ φ).mp (hm.symm ▸ hunit)
  have hi:U⁻¹=P⁻¹.submatrix φ φ:=by
    rw [←hm]
    exact Matrix.inv_submatrix_equiv P φ φ
  have hir:∀i:E,∑j:E,‖P⁻¹ (φ i) (φ j)‖≤C:=by
    rw [hi] at hr
    exact hr
  have hic:∀j:E,∑i:E,‖P⁻¹ (φ i) (φ j)‖≤C:=by
    rw [hi] at hc
    exact hc
  refine ⟨hu,?_,?_⟩
  · intro v
    rw [←φ.sum_comp (fun w:T=>‖P⁻¹ v w‖)]
    simpa only [φ.apply_symm_apply] using hir (φ.symm v)
  · intro w
    rw [←φ.sum_comp (fun v:T=>‖P⁻¹ v w‖)]
    simpa only [φ.apply_symm_apply] using hic (φ.symm w)

end LocalLaw
