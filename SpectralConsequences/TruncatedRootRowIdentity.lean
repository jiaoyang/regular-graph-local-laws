import LocalLaw.CavityMinorRowIdentity

/-! Exact full-root Schur expansion with the deterministic old truncated model. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance truncatedRootRowIdentityDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ} {ι:Type} [Fintype ι]

def truncatedBoundaryInner (g:LocalLaw.RegularGraph N d) (T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T) (i:ι):T:=
  ⟨(labels i).val.1,(labels i).property.2.1⟩

theorem truncated_new_coupling_reindex (g:LocalLaw.RegularGraph N d) (T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T) (selector:ℕ):
    let s:=g.admissibleState T labels samples
    let new:=g.labelledResampledGraph T labels samples selector
    (cutInnerCoupling new.graph d T).submatrix id (s.fullResample selector).boundary=
      indexedBoundaryCoupling (truncatedBoundaryInner g T labels) (treeEdgeWeight d):=by
  dsimp only
  ext v i
  have hfirst:(((g.admissibleState T labels samples).fullResample selector).boundary i).val.1=
      (labels i).val.1:=(g.admissibleState T labels samples).fullResample_boundary_inner_endpoint selector i
  have hp:v.val=(labels i).val.1↔v=truncatedBoundaryInner g T labels i:=by
    constructor
    · exact fun h=>Subtype.ext h
    · exact fun h=>congrArg Subtype.val h
  simp only [Matrix.submatrix_apply,id_eq,cutInnerCoupling,indexedBoundaryCoupling,hfirst,hp]
  rfl

theorem truncated_root_row_identity (g:LocalLaw.RegularGraph N d) (hd:3≤d) (T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T) (selector:ℕ)
    (q z:ℂ) (hz:0<z.im) (hq:0≤q.im) (root:T):
    let new:=g.labelledResampledGraph T labels samples selector
    let R:=(new.G z).submatrix (Subtype.val:T→Fin N) (Subtype.val:T→Fin N)
    let P:=(g.deficient.restrict T).extensionGreen q z
    let l:=truncatedBoundaryInner g T labels
    let D:=g.sourceTruncatedBoundaryDefect T labels samples selector q z
    ∀v,R root v-P root v=(treeEdgeWeight d)^2*(∑i,∑j,P root (l i)*D i j*P (l j) v)+
      (treeEdgeWeight d)^2*(∑i,∑j,(R root (l i)-P root (l i))*D i j*P (l j) v):=by
  dsimp only
  let s:=g.admissibleState T labels samples
  let new:=g.labelledResampledGraph T labels samples selector
  let R:=(new.G z).submatrix (Subtype.val:T→Fin N) (Subtype.val:T→Fin N)
  let P:=(g.deficient.restrict T).extensionGreen q z
  let l:=truncatedBoundaryInner g T labels
  let U:=indexedBoundaryCoupling l (treeEdgeWeight d)
  let Unew:=cutInnerCoupling new.graph d T
  let Dnew:=new.truncatedBoundaryDefect T q z
  let D:=g.sourceTruncatedBoundaryDefect T labels samples selector q z
  let e:=(s.fullResample selector).boundary
  have hU:Unew.submatrix id e=U:=truncated_new_coupling_reindex g T labels samples selector
  have hUt:Unew.transpose.submatrix e id=U.transpose:=by
    ext i v
    exact congrFun (congrFun hU v) i
  have hD:Dnew.submatrix e e=D:=(g.sourceTruncatedBoundaryDefect_eq_actual T labels samples selector q z).symm
  have hm:Unew*Dnew*Unew.transpose=U*D*U.transpose:=by
    exact (sandwich_equiv_middle Unew Dnew Unew.transpose e).trans
      (congrArg₂ (·*·) (congrArg₂ (·*·) hU hD) hUt)
  have h:=new.truncated_boundary_retained_expansion hd T q z hz hq
  dsimp only at h
  rw [g.resampled_truncated_extensionGreen_eq T labels samples selector q z] at h
  change R-P=P*(Unew*Dnew*Unew.transpose)*P+(R-P)*(Unew*Dnew*Unew.transpose)*P at h
  rw [hm] at h
  have hp:P*(U*D*U.transpose)*P=(P*U)*D*(U.transpose*P):=by simp only [Matrix.mul_assoc]
  have hr:(R-P)*(U*D*U.transpose)*P=((R-P)*U)*D*(U.transpose*P):=by simp only [Matrix.mul_assoc]
  rw [hp,hr] at h
  intro v
  have he:=congrFun (congrFun h root) v
  simp only [Matrix.sub_apply,Matrix.add_apply] at he
  rw [indexedBoundary_sandwich_row,indexedBoundary_sandwich_row] at he
  exact he

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.truncated_root_row_identity
