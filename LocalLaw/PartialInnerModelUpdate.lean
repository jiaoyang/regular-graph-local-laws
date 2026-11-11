import LocalLaw.PartialInnerPrecision
import LocalLaw.EmbeddedFiniteRankResolvent

/-! True inverse updates for partial deletion of the inner ball. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialInnerModelUpdateDecidable (p:Prop):Decidable p:=Classical.propDecidable p
set_option maxHeartbeats 3000000
namespace LabelledResamplingState
variable {V:Type}{T:Set V}{ι:Type}

theorem partialInner_away_endpoints (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set V)
    (x:((s.retainedInnerSet S)ᶜ:Set S))
    (hx:x∉Set.range (s.partialInnerDeletedEmbedding selector S)):
    x.val.val∉s.fullResampleEndpoints selector:=by
  let K:=s.fullSliceOutside S
  let v:K:=⟨⟨x.val.val,x.property⟩,x.val.property⟩
  have hv:v∉Set.range (s.partialEndpointEmbedding selector K):=by
    rintro ⟨i,hi⟩
    apply hx
    refine ⟨i,?_⟩
    exact Subtype.ext (Subtype.ext (congrArg (fun u:K=>u.val.val) hi))
  have ho:v.val∉s.fullResampleOutsideEndpoints selector:=by
    rintro ⟨i,hi,hxi⟩
    apply hv
    apply (s.partialEndpointEmbedding_range selector K v).mpr
    exact ⟨⟨i,hi⟩,hxi⟩
  rintro ⟨i,hi,hxi⟩
  change x.val.val=(s.quad i).a∨x.val.val∈(s.quad i).exterior at hxi
  rcases hxi with hin|hex
  · have hnot:x.val.val∉T:=x.property
    exact hnot (hin.symm ▸ sampledSwitching_root_mem s.graph T s.samples (s.boundary i))
  · exact ho ⟨i,hi,hex⟩

end LabelledResamplingState
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

theorem partial_inner_model_difference_supported (g:RegularGraph N d)(hd:3≤d)
    (T:Set (Fin N))(labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Fin N))(q z:ℂ):
    let s:=g.admissibleState T labels samples
    let Tm:=s.retainedInnerSet S
    let old:=(g.deficient.restrict S).delete Tm
    let new:=((g.labelledResampledGraph T labels samples selector).deficient.restrict S).delete Tm
    let e:=s.partialInnerDeletedEmbedding selector S
    ∀x y,x∉Set.range e∨y∉Set.range e→(new.extensionMatrix q z-old.extensionMatrix q z) x y=0:=by
  dsimp only
  let s:=g.admissibleState T labels samples
  let old:=g.deficient.restrict S
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.restrict S
  let e:=s.partialInnerDeletedEmbedding selector S
  have hm:=old.extensionMatrix_difference_row_charge new hd (fun _=>rfl) q z
  have hrow (x:S)(hx:x.val∉s.fullResampleEndpoints selector):
      ∀y:S,(new.H-old.H) x y=0:=by
    intro y
    have hh:=s.fullResample_adj_agrees_off_endpoints selector x.val y.val (Or.inl hx)
    simp only [DeficientGraph.H,normalizedAdjacency,Matrix.sub_apply,Matrix.smul_apply,
      smul_eq_mul,SimpleGraph.adjMatrix_apply]
    change (treeEdgeWeight d)*(if (s.fullResample selector).graph.Adj x.val y.val then 1 else 0)-
      (treeEdgeWeight d)*(if s.graph.Adj x.val y.val then 1 else 0)=0
    rw [←hh,sub_self]
  intro x y hxy
  rw [old.extensionMatrix_delete,new.extensionMatrix_delete]
  change (new.extensionMatrix q z-old.extensionMatrix q z) x.val y.val=0
  rw [hm]
  have hdiff:(new.H-old.H) x.val y.val=0:=by
    rcases hxy with hx|hy
    · exact hrow x.val (s.partialInner_away_endpoints selector S x hx) y.val
    · have hh:=hrow y.val (s.partialInner_away_endpoints selector S y hy) x.val
      simpa only [Matrix.sub_apply,DeficientGraph.H,normalizedAdjacency,Matrix.smul_apply,
        smul_eq_mul,SimpleGraph.adjMatrix_apply,new.graph.adj_comm,old.graph.adj_comm] using hh
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply,hdiff,zero_add]
  by_cases he:x.val=y.val
  · have hsame:x=y:=Subtype.ext he
    subst y
    have hx:x∉Set.range e:=hxy.elim id id
    have hr:=hrow x.val (s.partialInner_away_endpoints selector S x hx)
    simp only [if_true,hr,Finset.sum_const_zero,mul_zero]
  · simp only [he,if_false,mul_zero]

theorem partial_inner_model_endpoint_updates (g:RegularGraph N d)(hd:3≤d)
    (T:Set (Fin N))(labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Fin N))(q z:ℂ)(hz:0<z.im)(hq:0≤q.im):
    let s:=g.admissibleState T labels samples
    let Tm:=s.retainedInnerSet S
    let old:=(g.deficient.restrict S).delete Tm
    let new:=((g.labelledResampledGraph T labels samples selector).deficient.restrict S).delete Tm
    let e:=s.partialInnerDeletedEmbedding selector S
    let K:=s.fullSliceOutside S
    let W:Matrix (s.PartialEndpointIndex selector (s.fullSliceOutside S))
      (s.PartialEndpointIndex selector (s.fullSliceOutside S)) ℂ:=partialTripleEdgeUpdate (s.partialBoundaryMask selector K) (s.partialFirstMask selector K)
      (s.partialSecondMask selector K) (treeEdgeWeight d)+
      partialLMaskCharge (s.partialBoundaryMask selector K) (s.partialFirstMask selector K)
      (s.partialSecondMask selector K) (s.retainedInnerLabels selector S) q (treeEdgeWeight d)
    let R:=(old.extensionGreen q z).submatrix e e
    let U:=(new.extensionGreen q z).submatrix e e
    (U+R*W*U=R)∧(U+U*W*R=R):=by
  dsimp only
  let s:=g.admissibleState T labels samples
  let Tm:=s.retainedInnerSet S
  let old:=(g.deficient.restrict S).delete Tm
  let new:=((g.labelledResampledGraph T labels samples selector).deficient.restrict S).delete Tm
  let e:=s.partialInnerDeletedEmbedding selector S
  have hh:=inverse_embedded_finite_rank_updates (old.extensionMatrix q z) (new.extensionMatrix q z)
    (old.extensionMatrix_isUnit hd q z hz hq) (new.extensionMatrix_isUnit hd q z hz hq) e
    (g.partial_inner_model_difference_supported hd T labels samples selector S q z)
  dsimp only at hh
  rw [g.partial_inner_deleted_precision_coupling hd T labels samples selector S q z] at hh
  exact hh

end RegularGraph
end LocalLaw
