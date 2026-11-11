import LocalLaw.FullOldTwoTargetGeometry
import LocalLaw.FullEndpointMasks
import LocalLaw.TwoTargetRowExtension

/-! Exact full surgery support and ball capture in the old two-target model. -/
noncomputable section
namespace LocalLaw
local instance fullAugmentedCaptureDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} [Fintype V] {T : Set V} {ι : Type} [Fintype ι]

omit [Fintype V] [Fintype ι] in
theorem fullPartialEmbedding_mem_roots (s : LabelledResamplingState V T ι)
    (selector : ℕ) (S : Set V) (hs : 1≤selector) (i : s.FullEndpointIndex selector S) :
    (s.fullPartialEmbedding selector S hs i).val∈s.fullEndpointRoots selector := by
  rcases i with v | (b | c)
  · rcases v.property.2 with hT | ⟨u,hu,he⟩
    · exact Or.inl hT
    · exact Or.inr ⟨u,Or.inl hu,he⟩
  · exact Or.inr ⟨s.admissibleSampleVertex selector b.val,
      Or.inr (Set.mem_iUnion.mpr ⟨b.val,Or.inl rfl⟩),rfl⟩
  · exact Or.inr ⟨s.admissibleSecondVertex selector c.val,
      Or.inr (Set.mem_iUnion.mpr ⟨c.val,Or.inr rfl⟩),rfl⟩

omit [Fintype V] [Fintype ι] in
theorem fullTwoTarget_contains_endpoints (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (x y : V) : s.fullResampleEndpoints selector⊆s.fullTwoTargetVertices selector r x y := by
  intro v hv
  rw [s.fullTwoTarget_eq_setBall]
  exact ⟨v,Or.inl (s.fullResampleEndpoints_subset_fullEndpointRoots selector hv),by simp⟩

omit [Fintype V] in
theorem fullTwoTarget_supported_on_augmented_index (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (hs : 1≤selector) (x y : V) :
    let S:=s.fullTwoTargetVertices selector r x y
    let xl:=twoBallLeft s.graph (filledExteriorVertices T (s.endpointModelVertices selector r)) x y r
    let yl:=twoBallRight s.graph (filledExteriorVertices T (s.endpointModelVertices selector r)) x y r
    let e0:=s.fullPartialEmbedding selector S hs
    let I:=twoTargetIndexSet e0 xl yl
    let e:I↪S:=⟨Subtype.val,Subtype.val_injective⟩
    ∀u v,u∉Set.range (fun i:I=>(e i).val)∨v∉Set.range (fun i:I=>(e i).val)→
      (s.graph.Adj u v↔(s.fullResample selector).graph.Adj u v) := by
  dsimp only
  let S:=s.fullTwoTargetVertices selector r x y
  let xl:=twoBallLeft s.graph (filledExteriorVertices T (s.endpointModelVertices selector r)) x y r
  let yl:=twoBallRight s.graph (filledExteriorVertices T (s.endpointModelVertices selector r)) x y r
  let e0:=s.fullPartialEmbedding selector S hs
  let I:=twoTargetIndexSet e0 xl yl
  let e:I↪S:=⟨Subtype.val,Subtype.val_injective⟩
  have haway (u:V)(hu:u∉Set.range (fun i:I=>(e i).val)) : u∉s.fullResampleEndpoints selector := by
    intro hm
    let us:S:=⟨u,s.fullTwoTarget_contains_endpoints selector r x y hm⟩
    obtain ⟨i,hi⟩:=s.fullPartialEmbedding_captures selector S hs us hm
    exact hu ⟨⟨e0 i,Or.inl ⟨i,rfl⟩⟩,congrArg Subtype.val hi⟩
  intro u v h
  exact s.fullResample_adj_agrees_off_endpoints selector u v (h.imp (haway u) (haway v))

end LabelledResamplingState
end LocalLaw
