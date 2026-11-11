import LocalLaw.PartialInnerModelUpdate

/-! Actual finite coupling mass for partial-T models. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialInnerCouplingMassDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

theorem partial_inner_coupling_mass (g:RegularGraph N d)(hd:3≤d)
    (T:Set (Fin N))(labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Fin N))(q z:ℂ):
    let s:=g.admissibleState T labels samples
    let Tm:=s.retainedInnerSet S
    let old:=(g.deficient.restrict S).delete Tm
    let new:=((g.labelledResampledGraph T labels samples selector).deficient.restrict S).delete Tm
    let e:=s.partialInnerDeletedEmbedding selector S
    ∀i,∑j,‖(new.extensionMatrix q z-old.extensionMatrix q z) (e i) (e j)‖≤
      2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2:=by
  dsimp only
  let s:=g.admissibleState T labels samples
  let K:=s.fullSliceOutside S
  let I:=s.PartialEndpointIndex selector K
  let A:=s.partialBoundaryMask selector K
  let B:=s.partialFirstMask selector K
  let C:=s.partialSecondMask selector K
  let J:=A⊕(B⊕C)
  let φ:I≃J:=Equiv.refl _
  let W:Matrix J J ℂ:=partialTripleEdgeUpdate A B C (treeEdgeWeight d)+
    partialLMaskCharge A B C (s.retainedInnerLabels selector S) q (treeEdgeWeight d)
  have he:=g.partial_inner_deleted_precision_coupling hd T labels samples selector S q z
  have hm:=partialLMaskCoupling_mass A B C (s.retainedInnerLabels selector S) q (treeEdgeWeight d)
  intro i
  calc
    _=∑j:I,‖W (φ i) (φ j)‖:=by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg norm (congrArg (fun M:Matrix I I ℂ=>M i j) he)
    _=∑j:J,‖W (φ i) j‖:=φ.sum_comp (fun j=>‖W (φ i) j‖)
    _≤_:=hm.1 (φ i)

end RegularGraph
end LocalLaw
