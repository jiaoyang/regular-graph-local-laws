import LocalLaw.DeletedBoundaryColumns
import LocalLaw.FilledModelDiameter
import LocalLaw.FilledBoundarySchur

/-! # Boundary columns of the literal filled exterior model -/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance filledOutsideColumnsDecidable (p:Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}

def filledBoundaryEdgeEquiv (g:RegularGraph N d) (T:Set (Fin N)) (K:Set (Tᶜ:Set (Fin N)))
    (hK:∀α:BoundaryOrientedEdge g.graph T,boundaryOutsideVertex g.graph T α∈K) :
    BoundaryOrientedEdge (g.filledExteriorModel T K).graph (filledExteriorInner T K) ≃ BoundaryOrientedEdge g.graph T where
  toFun e:=⟨(e.val.1.val,e.val.2.val),e.property.1,e.property.2.1,e.property.2.2⟩
  invFun e:=⟨(⟨e.val.1,Or.inl e.property.2.1⟩,
      ⟨e.val.2,Or.inr ⟨boundaryOutsideVertex g.graph T e,hK e,rfl⟩⟩),
      e.property.1,e.property.2.1,e.property.2.2⟩
  left_inv e:=by apply Subtype.ext; apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv e:=rfl

theorem filledOutside_boundary_column (g:RegularGraph N d) (hd:3≤d)
    (T:Set (Fin N)) (K:Set (Tᶜ:Set (Fin N)))
    (hK:∀α:BoundaryOrientedEdge g.graph T,boundaryOutsideVertex g.graph T α∈K)
    (hT:(g.graph.induce T).Connected) (hbase:(g.filledExteriorModel T K).ComponentReferenceBudget)
    (R:ℕ) (hR:∀x y,(g.filledExteriorModel T K).graph.dist x y≤R)
    (q z:ℂ) (hz:0<z.im) (hq:0≤q.im)
    (small:‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*coreConvolutionConstant (finiteOmega d+1)*
      (((finiteOmega d+1)*(2*R+1):ℕ)+1:ℝ)≤1/2) (j:K) :
    (∑α:BoundaryOrientedEdge g.graph T,
      ‖((g.deficient.delete T).restrict K).extensionGreen q z (g.filledBoundaryVertex T K hK α) j‖)≤
        2*finiteExtraReferenceConstant d*(finiteOmega d+1) := by
  let M:=g.filledExteriorModel T K
  let I:=filledExteriorInner T K
  let φ:=filledBoundaryEdgeEquiv g T K hK
  let ψ:=filledExteriorOutsideIso g.graph T K
  have hI:(M.graph.induce I).Connected := (filledInnerGraphIso g.graph T K).connected_iff.mpr hT
  have hMzero:∀v,M.deficit v=0 := fun _=>rfl
  have hbound:=M.componentwise_deleted_boundary_column hd hMzero hbase I hI R hR q z hz hq small (ψ.symm j)
  have hmatrix:=g.deficient.filledExterior_deleted_extensionGreen T K q z
  change (((g.deficient.delete T).restrict K).extensionGreen q z).submatrix ψ ψ=(M.delete I).extensionGreen q z at hmatrix
  have hpoint (α:BoundaryOrientedEdge M.graph I) :
      ‖(M.delete I).extensionGreen q z (boundaryOutsideVertex M.graph I α) (ψ.symm j)‖=
      ‖((g.deficient.delete T).restrict K).extensionGreen q z (g.filledBoundaryVertex T K hK (φ α)) j‖ := by
    rw [←hmatrix]
    simp only [Matrix.submatrix_apply,ψ.apply_symm_apply]
    rfl
  calc
    _ = ∑α:BoundaryOrientedEdge M.graph I,
        ‖(M.delete I).extensionGreen q z (boundaryOutsideVertex M.graph I α) (ψ.symm j)‖ := by
      symm
      exact Fintype.sum_equiv φ _ _ hpoint
    _ ≤ _ := hbound

end RegularGraph
end LocalLaw
