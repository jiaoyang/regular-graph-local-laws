import LocalLaw.CommonDeletedPairCapture
import LocalLaw.PartialFirstDeletionCaps

/-! # Actual common-deleted capture inside any old restriction

Deleting the retained selected first vertices maps injectively into the
global physically common deleted graph. Thus its target pair balls are
captured by the actual switched pair set, independently of ball capture in
the original restriction.
-/

noncomputable section
namespace LocalLaw
namespace LabelledResamplingState
variable {V:Type}{T:Set V}{ι:Type}[Fintype ι]

omit [Fintype ι] in
theorem selectedFirstSet_subset_twoTarget (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(x y:(Tᶜ:Set V)) :
    s.selectedFirstSet selector⊆s.twoTargetEndpointVertices selector r x y := by
  rintro a ⟨i,rfl⟩
  apply s.endpointModelVertices_subset_twoTargetEndpointVertices selector r x y
  exact ⟨s.admissibleSampleVertex selector i,
    Or.inr (Set.mem_iUnion.mpr ⟨i,Or.inl rfl⟩),by
      change (outsideGraph s.graph T).edist (s.admissibleSampleVertex selector i)
        (s.admissibleSampleVertex selector i)≤(r:ℕ∞)
      rw [SimpleGraph.edist_self]
      exact bot_le⟩

def selectedCommonEmbedding (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V)) :
    ((s.partialFirstRemovedSet selector S)ᶜ:Set S)↪
      ((s.selectedFirstSet selector)ᶜ:Set (Tᶜ:Set V)) where
  toFun v:=⟨v.val.val,v.property⟩
  inj':=by
    intro v w h
    have hv:v.val.val=w.val.val:=congrArg
      (fun a:((s.selectedFirstSet selector)ᶜ:Set (Tᶜ:Set V))=>a.val) h
    exact Subtype.ext (Subtype.ext hv)

def selectedCommonHom (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V)) :
    outsideGraph ((outsideGraph s.graph T).induce S) (s.partialFirstRemovedSet selector S)→g
      (outsideGraph s.graph T).induce (s.selectedFirstSet selector)ᶜ where
  toFun:=s.selectedCommonEmbedding selector S
  map_rel':=fun h=>h

theorem selectedCommon_pairBall_capture (s:LabelledResamplingState V T ι)(selector r:ℕ)
    (S:Set (Tᶜ:Set V))
    (x y:((s.partialFirstRemovedSet selector S)ᶜ:Set S)) :
    pairBallVertices (outsideGraph ((outsideGraph s.graph T).induce S)
      (s.partialFirstRemovedSet selector S)) x y r⊆
      {v:((s.partialFirstRemovedSet selector S)ᶜ:Set S) |
        v.val.val∈pairBallVertices (outsideGraph (s.fullResample selector).graph T) x.val.val y.val.val r} := by
  intro v hv
  have hcommon : (s.selectedCommonEmbedding selector S v)∈
      pairBallVertices ((outsideGraph s.graph T).induce (s.selectedFirstSet selector)ᶜ)
        (s.selectedCommonEmbedding selector S x) (s.selectedCommonEmbedding selector S y) r := by
    rcases hv with hx | hy
    · exact Or.inl ((graphHom_edist_le (s.selectedCommonHom selector S) x v).trans hx)
    · exact Or.inr ((graphHom_edist_le (s.selectedCommonHom selector S) y v).trans hy)
  exact s.common_deleted_pairBall_subset_new_pair selector r
    (s.selectedCommonEmbedding selector S x) (s.selectedCommonEmbedding selector S y) hcommon

end LabelledResamplingState
end LocalLaw
