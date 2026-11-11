import LocalLaw.PartialInnerMasks
import LocalLaw.FullBoundarySwitchRows
import LocalLaw.FullRetainedPrecision
import LocalLaw.PartialLMaskSurgery

/-! Literal L-mask precision after deleting only retained inner vertices. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialInnerPrecisionDecidable (p:Prop):Decidable p:=Classical.propDecidable p
set_option maxHeartbeats 3000000
namespace LabelledResamplingState
variable {V:Type}[Fintype V]{T:Set V}{ι:Type}[Fintype ι]

theorem partialInner_retained_charge (s:LabelledResamplingState V T ι)
    (selector:ℕ)(S:Set V)(q α:ℂ):
    (fun u v:s.PartialEndpointIndex selector (s.fullSliceOutside S)=>
      q*α^2*(if u=v then s.fullRetainedRowDelta selector S
        (s.partialEndpointEmbedding selector (s.fullSliceOutside S) u).val.val else 0))=
    partialLMaskCharge (s.partialBoundaryMask selector (s.fullSliceOutside S))
      (s.partialFirstMask selector (s.fullSliceOutside S))
      (s.partialSecondMask selector (s.fullSliceOutside S)) (s.retainedInnerLabels selector S) q α:=by
  ext u v
  by_cases huv:u=v
  · subst v
    simp only [if_true]
    rcases u with a|(b|c)
    · change q*α^2*(s.fullRetainedRowDelta selector S (s.admissibleBoundaryVertex selector a.val).val)=_
      rw [s.fullRetainedRowDelta_boundary]
      simp only [partialLMaskCharge,Matrix.diagonal_apply_eq,partialBoundaryMask,partialFirstMask,
        partialSecondMask,fullSliceOutside,retainedInnerLabels,Set.mem_setOf_eq]
    · change q*α^2*(s.fullRetainedRowDelta selector S (s.admissibleSampleVertex selector b.val).val)=_
      rw [s.fullRetainedRowDelta_first]
      simp only [partialLMaskCharge,Matrix.diagonal_apply_eq,partialBoundaryMask,partialFirstMask,
        partialSecondMask,fullSliceOutside,retainedInnerLabels,Set.mem_setOf_eq]
    · change q*α^2*(s.fullRetainedRowDelta selector S (s.admissibleSecondVertex selector c.val).val)=_
      rw [s.fullRetainedRowDelta_second]
      simp only [partialLMaskCharge,Matrix.diagonal_apply_eq,partialBoundaryMask,partialFirstMask,
        partialSecondMask,fullSliceOutside,retainedInnerLabels,Set.mem_setOf_eq]
  · simp only [huv,if_false,mul_zero,partialLMaskCharge,Matrix.diagonal_apply,if_false]

theorem partialInner_edge_update (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set V)(α:ℂ):
    (fun u v:s.PartialEndpointIndex selector (s.fullSliceOutside S)=>
      α*((if (outsideGraph (s.fullResample selector).graph T).Adj
        (s.partialEndpointEmbedding selector (s.fullSliceOutside S) u).val
        (s.partialEndpointEmbedding selector (s.fullSliceOutside S) v).val then 1 else 0)-
        (if (outsideGraph s.graph T).Adj
        (s.partialEndpointEmbedding selector (s.fullSliceOutside S) u).val
        (s.partialEndpointEmbedding selector (s.fullSliceOutside S) v).val then 1 else 0)))=
    partialTripleEdgeUpdate (s.partialBoundaryMask selector (s.fullSliceOutside S))
      (s.partialFirstMask selector (s.fullSliceOutside S))
      (s.partialSecondMask selector (s.fullSliceOutside S)) α:=by
  have hzero:partialTripleCharge (s.partialBoundaryMask selector (s.fullSliceOutside S))
      (s.partialFirstMask selector (s.fullSliceOutside S))
      (s.partialSecondMask selector (s.fullSliceOutside S)) (0:ℂ) α=0:=by
    ext u v
    rcases u with a|(b|c) <;> simp [partialTripleCharge,Matrix.diagonal_apply]
  have hh:=s.partialActualCoupling_eq selector (s.fullSliceOutside S) 0 α
  rw [hzero,add_zero] at hh
  ext u v
  have he:=congrArg (fun M:Matrix (s.PartialEndpointIndex selector (s.fullSliceOutside S))
    (s.PartialEndpointIndex selector (s.fullSliceOutside S)) ℂ=>M u v) hh
  change α*((if (outsideGraph (s.fullResample selector).graph T).Adj
    (s.partialEndpointEmbedding selector (s.fullSliceOutside S) u).val
    (s.partialEndpointEmbedding selector (s.fullSliceOutside S) v).val then 1 else 0)-
    (if (outsideGraph s.graph T).Adj
    (s.partialEndpointEmbedding selector (s.fullSliceOutside S) u).val
    (s.partialEndpointEmbedding selector (s.fullSliceOutside S) v).val then 1 else 0))-
    0*α^2*(if u=v then _ else 0)=_ at he
  simpa only [zero_mul,sub_zero] using he

end LabelledResamplingState
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

theorem partial_inner_deleted_precision_coupling (g:RegularGraph N d)(hd:3≤d)
    (T:Set (Fin N))(labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Fin N))(q z:ℂ):
    let s:=g.admissibleState T labels samples
    let Tm:=s.retainedInnerSet S
    let old:=(g.deficient.restrict S).delete Tm
    let new:=((g.labelledResampledGraph T labels samples selector).deficient.restrict S).delete Tm
    let e:=s.partialInnerDeletedEmbedding selector S
    (new.extensionMatrix q z-old.extensionMatrix q z).submatrix e e=
      partialTripleEdgeUpdate (s.partialBoundaryMask selector (s.fullSliceOutside S))
        (s.partialFirstMask selector (s.fullSliceOutside S))
        (s.partialSecondMask selector (s.fullSliceOutside S)) (treeEdgeWeight d)+
      partialLMaskCharge (s.partialBoundaryMask selector (s.fullSliceOutside S))
        (s.partialFirstMask selector (s.fullSliceOutside S))
        (s.partialSecondMask selector (s.fullSliceOutside S)) (s.retainedInnerLabels selector S)
        q (treeEdgeWeight d):=by
  dsimp only
  let s:=g.admissibleState T labels samples
  let Tm:=s.retainedInnerSet S
  let old:=g.deficient.restrict S
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.restrict S
  let e:=s.partialInnerDeletedEmbedding selector S
  let ep:=s.partialEndpointEmbedding selector (s.fullSliceOutside S)
  let α:=treeEdgeWeight d
  have hm:=old.extensionMatrix_difference_row_charge new hd (fun _=>rfl) q z
  have hrow (u:s.PartialEndpointIndex selector (s.fullSliceOutside S)):
      (∑v:S,(new.H-old.H) (e u).val v)=α*s.fullRetainedRowDelta selector S (ep u).val.val:=by
    dsimp only [LabelledResamplingState.fullRetainedRowDelta]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    simp only [DeficientGraph.H,normalizedAdjacency,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      SimpleGraph.adjMatrix_apply,LabelledResamplingState.fullRetainedRowDelta]
    change α*(if (s.fullResample selector).graph.Adj (ep u).val.val v.val then 1 else 0)-
      α*(if s.graph.Adj (ep u).val.val v.val then 1 else 0)=_
    ring
  have hrow' (u:s.PartialEndpointIndex selector (s.fullSliceOutside S)):
      (∑v:S,(new.H (e u).val v-old.H (e u).val v))=α*s.fullRetainedRowDelta selector S (ep u).val.val:=hrow u
  rw [←s.partialInner_edge_update selector S α,←s.partialInner_retained_charge selector S q α]
  ext u v
  have hh:=congrArg (fun M:Matrix S S ℂ=>M (e u).val (e v).val) hm
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.diagonal_apply,e.injective.eq_iff] at hh
  rw [old.extensionMatrix_delete,new.extensionMatrix_delete]
  change (new.extensionMatrix q z) (e u).val (e v).val-(old.extensionMatrix q z) (e u).val (e v).val=_
  rw [hh]
  have heq:((e u).val=(e v).val)↔u=v:=by
    constructor
    · intro h
      exact e.injective (Subtype.ext h)
    · exact congrArg (fun i=>(e i).val)
  simp only [heq]
  rw [hrow']
  have hH:new.H (e u).val (e v).val-old.H (e u).val (e v).val=
      α*((if (outsideGraph (s.fullResample selector).graph T).Adj (ep u).val (ep v).val then 1 else 0)-
        (if (outsideGraph s.graph T).Adj (ep u).val (ep v).val then 1 else 0)):=by
    simp only [DeficientGraph.H,normalizedAdjacency,Matrix.sub_apply,Matrix.smul_apply,
      smul_eq_mul,SimpleGraph.adjMatrix_apply]
    change α*(if (outsideGraph (s.fullResample selector).graph T).Adj (ep u).val (ep v).val then 1 else 0)-
      α*(if (outsideGraph s.graph T).Adj (ep u).val (ep v).val then 1 else 0)=_
    ring
  rw [hH]
  dsimp only [Matrix.add_apply]
  have halg (x y:ℂ):x+(q*α)*(α*y)=x+q*α^2*y:=by ring
  by_cases huv:u=v
  · simp only [huv,if_true]
    exact halg _ _
  · simp only [huv,if_false,mul_zero,add_zero]
    rfl

end RegularGraph
end LocalLaw
