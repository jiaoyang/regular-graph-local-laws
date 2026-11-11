import LocalLaw.PartialFirstDeletionCaps

/-! # Retained old boundary roots survive deletion of all selected first endpoints -/

noncomputable section
namespace LocalLaw
local instance commonBoundaryEmbeddingDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type}

theorem partialBoundaryEmbedding_not_removedFirst (s : LabelledResamplingState V T ι)
    (selector : ℕ) (S : Set (Tᶜ:Set V)) (i : s.partialBoundaryMask selector S) :
    s.partialBoundaryEmbedding selector S i∉s.partialFirstRemovedSet selector S := by
  intro hi
  change (s.partialBoundaryEmbedding selector S i).val∈s.selectedFirstSet selector at hi
  obtain ⟨j,hj⟩:=hi
  have hf:=s.admissibleSampleVertex_far_boundary selector j (s.boundary i.val.val)
  change (selector:ℕ∞)<(outsideGraph s.graph T).edist
    (s.admissibleSampleVertex selector j) (s.admissibleBoundaryVertex selector i.val) at hf
  have he : s.admissibleSampleVertex selector j=s.admissibleBoundaryVertex selector i.val := hj
  rw [he,SimpleGraph.edist_self] at hf
  exact (not_lt_of_ge (bot_le:(0:ℕ∞)≤selector)) hf

def partialBoundaryCoreEmbedding (s : LabelledResamplingState V T ι) (selector : ℕ)
    (S : Set (Tᶜ:Set V)) : s.partialBoundaryMask selector S↪((s.partialFirstRemovedSet selector S)ᶜ:Set S) where
  toFun i:=⟨s.partialBoundaryEmbedding selector S i,s.partialBoundaryEmbedding_not_removedFirst selector S i⟩
  inj':=by
    intro i j hij
    exact (s.partialBoundaryEmbedding selector S).injective (congrArg Subtype.val hij)

theorem partialBoundaryCoreEmbedding_separated (s : LabelledResamplingState V T ι)
    (selector : ℕ) (S : Set (Tᶜ:Set V)) (i j : s.partialBoundaryMask selector S) (hij : i≠j) :
    (selector:ℕ∞)<(((outsideGraph s.graph T).induce S).induce
      ((s.partialFirstRemovedSet selector S)ᶜ:Set S)).edist
        (s.partialBoundaryCoreEmbedding selector S i) (s.partialBoundaryCoreEmbedding selector S j) := by
  let f : (((outsideGraph s.graph T).induce S).induce
      ((s.partialFirstRemovedSet selector S)ᶜ:Set S))→g(outsideGraph s.graph T) :=
    {toFun:=fun v=>v.val.val,map_rel':=fun h=>h}
  exact (s.partialBoundaryEmbedding_separated selector S i j hij).trans_le
    (graphHom_edist_le f (s.partialBoundaryCoreEmbedding selector S i) (s.partialBoundaryCoreEmbedding selector S j))

end LabelledResamplingState
end LocalLaw
