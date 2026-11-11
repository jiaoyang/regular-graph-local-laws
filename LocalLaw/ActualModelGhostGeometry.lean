import LocalLaw.AugmentedPairCapture
import LocalLaw.PairBoundaryDepth

/-! # The actual completion vertices are confined to the fixed endpoint model

The old augmented vertex set is the union of the NEW target pair ball and
the fixed old/new endpoint neighborhood. Every vertex removed in passing to
the new pair model is therefore an endpoint-neighborhood vertex, and every
crossing starts at the actual outer target layer.
-/
noncomputable section
namespace LocalLaw
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type} [Fintype ι]

theorem twoTargetEndpointVertices_eq_new_pair_union (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(x y:(Tᶜ:Set V)) :
    s.twoTargetEndpointVertices selector r x y=
      pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r∪
        s.endpointModelVertices selector r := by
  rw [s.twoTargetEndpointVertices_new_setBall selector r x y,
    s.endpointModelVertices_fullResample selector r]
  ext v
  constructor
  · rintro ⟨a,ha,hd⟩
    rcases ha with ha | (ha | ha)
    · exact Or.inr ⟨a,ha,hd⟩
    · exact Or.inl (Or.inl (ha ▸ hd))
    · exact Or.inl (Or.inr (ha ▸ hd))
  · rintro ((hx | hy) | ⟨a,ha,hd⟩)
    · exact ⟨x,Or.inr (Or.inl rfl),hx⟩
    · exact ⟨y,Or.inr (Or.inr rfl),hy⟩
    · exact ⟨a,Or.inl ha,hd⟩

theorem twoTarget_ghost_subset_endpointModel (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(x y:(Tᶜ:Set V)) :
    s.twoTargetEndpointVertices selector r x y\
      pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r⊆
        s.endpointModelVertices selector r := by
  rw [s.twoTargetEndpointVertices_eq_new_pair_union selector r x y]
  intro v hv
  exact hv.1.resolve_left hv.2

theorem twoTarget_ghost_crossing_depth (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(x y u v:(Tᶜ:Set V))
    (hu:u∈pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r)
    (hv:v∈s.twoTargetEndpointVertices selector r x y)
    (hvnot:v∉pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r)
    (huv:(outsideGraph (s.fullResample selector).graph T).Adj u v) :
    v∈s.endpointModelVertices selector r ∧
      (r:ℕ∞)≤(outsideGraph (s.fullResample selector).graph T).edist x u ∧
      (r:ℕ∞)≤(outsideGraph (s.fullResample selector).graph T).edist y u := by
  refine ⟨s.twoTarget_ghost_subset_endpointModel selector r x y ⟨hv,hvnot⟩,?_⟩
  exact pair_boundary_inner_edist_lower (outsideGraph (s.fullResample selector).graph T) x y r
    ⟨(u,v),huv,hu,hvnot⟩

end LabelledResamplingState
end LocalLaw
