import LocalLaw.PartialInnerWeakCovariance
import LocalLaw.PartialInnerRestoration

/-! Exact transport of the old L-mask covariance to the actual deleted model. -/
noncomputable section
namespace LocalLaw
local instance partialInnerCovarianceDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type}{T:Set V}{ι:Type}

def partialInnerOldCovariance (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set V)
    (G:Matrix ((s.retainedInnerSet S)ᶜ:Set S) ((s.retainedInnerSet S)ᶜ:Set S) ℂ)(q p α:ℂ):
    Matrix (s.PartialEndpointIndex selector (s.fullSliceOutside S))
      (s.PartialEndpointIndex selector (s.fullSliceOutside S)) ℂ:=
  Matrix.fromBlocks (G.submatrix (s.partialInnerBoundaryEmbedding selector S)
    (s.partialInnerBoundaryEmbedding selector S)) 0 0
    (partialSampleCovariance (s.partialFirstMask selector (s.fullSliceOutside S))
      (s.partialSecondMask selector (s.fullSliceOutside S)) q p α)
end LabelledResamplingState
namespace RegularGraph
variable {N d:ℕ}{ι:Type}

theorem partial_inner_covariance_transport (g:RegularGraph N d)
    (T:Set (Fin N))(labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Fin N))(q p z:ℂ):
    let s:=g.admissibleState T labels samples
    let Tm:=s.retainedInnerSet S
    let K:=s.fullSliceOutside S
    let G:=((g.deficient.partialInnerAmbient T S).restrict K).extensionGreen q z
    let H:=((g.deficient.restrict S).delete Tm).extensionGreen q z
    (H.submatrix (s.partialInnerDeletedEmbedding selector S) (s.partialInnerDeletedEmbedding selector S)=
      G.submatrix (s.partialEndpointEmbedding selector K) (s.partialEndpointEmbedding selector K))∧
    s.partialInnerOldCovariance selector S H q p (treeEdgeWeight d)=
      s.partialOldCovariance selector K G q p (treeEdgeWeight d):=by
  dsimp only
  let s:=g.admissibleState T labels samples
  let Tm:=s.retainedInnerSet S
  let K:=s.fullSliceOutside S
  let G:=((g.deficient.partialInnerAmbient T S).restrict K).extensionGreen q z
  let H:=((g.deficient.restrict S).delete Tm).extensionGreen q z
  let φ:=restrictionDeletionGraphIso g.graph S T Tm (fun _=>Iff.rfl)
  have hh:=g.deficient.partialInnerAmbient_restrict_green T S Tm (fun _=>Iff.rfl) q z
  have hentry (u v:((s.retainedInnerSet S)ᶜ:Set S)):
      H u v=G (φ u) (φ v):=by
    exact (congrArg (fun M:Matrix ((s.retainedInnerSet S)ᶜ:Set S) ((s.retainedInnerSet S)ᶜ:Set S) ℂ=>M u v) hh).symm
  constructor
  · ext i j
    exact hentry _ _
  · have hcore:(H.submatrix (s.partialInnerBoundaryEmbedding selector S) (s.partialInnerBoundaryEmbedding selector S))=
        G.submatrix (s.partialBoundaryEmbedding selector K) (s.partialBoundaryEmbedding selector K):=by
      ext a b
      exact hentry _ _
    unfold LabelledResamplingState.partialInnerOldCovariance LabelledResamplingState.partialOldCovariance
    rw [hcore]

end RegularGraph
end LocalLaw
