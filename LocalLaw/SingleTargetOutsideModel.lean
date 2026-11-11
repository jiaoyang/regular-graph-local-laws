import LocalLaw.SingleTargetFilledGeometry
import LocalLaw.FilledBoundarySchur

/-! # Literal outside restriction for the one-target filled model -/

noncomputable section
namespace LocalLaw
local instance singleTargetOutsideDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ} {ι:Type} [Fintype ι]

def singleTargetOutsideVertices (g:RegularGraph N d) (T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector r:ℕ) (y:Fin N) : Set (Tᶜ:Set (Fin N)) :=
  {v | v.val∈g.singleTargetFilledVertices T labels samples selector r y}

theorem singleTargetOutside_fill_eq (g:RegularGraph N d) (T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector r:ℕ) (y:Fin N) :
    filledExteriorVertices T (g.singleTargetOutsideVertices T labels samples selector r y)=
      g.singleTargetFilledVertices T labels samples selector r y := by
  ext v
  constructor
  · rintro (hv | ⟨u,hu,rfl⟩)
    · exact Or.inl (Or.inl hv)
    · exact hu
  · intro hv
    by_cases hT:v∈T
    · exact Or.inl hT
    · exact Or.inr ⟨⟨v,hT⟩,hv,rfl⟩

def singleTargetOutsideTargetVertex (g:RegularGraph N d) (T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector r:ℕ) (y:Fin N) (hy:y∉T) : g.singleTargetOutsideVertices T labels samples selector r y :=
  ⟨⟨y,hy⟩,Or.inr (Or.inl (center_mem_graphBall _ y r))⟩

theorem singleTargetOutside_boundary_capture (g:RegularGraph N d) (T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector r:ℕ) (y:Fin N) :
    ∀α:BoundaryOrientedEdge (g.labelledResampledGraph T labels samples selector).graph T,
      boundaryOutsideVertex _ T α∈g.singleTargetOutsideVertices T labels samples selector r y := by
  intro α
  let s:=g.admissibleState T labels samples
  exact Or.inl (Or.inr ⟨_,s.endpointModel_contains_new_boundary selector r α,rfl⟩)

theorem singleTargetOutside_inner_capture (g:RegularGraph N d) (T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector r:ℕ) (y:Fin N) (x:T) :
    graphBallVertices (g.labelledResampledGraph T labels samples selector).graph x.val (r+1)⊆
      filledExteriorVertices T (g.singleTargetOutsideVertices T labels samples selector r y) := by
  rw [g.singleTargetOutside_fill_eq]
  exact fun _ hv => Or.inl ((g.admissibleState T labels samples).filledEndpoint_captures_inner_ball selector r x hv)

theorem singleTargetOutside_geometry (g:RegularGraph N d) (T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector r:ℕ) (y:Fin N) (R:ℕ) (A L:ℝ)
    (h:SourceFullEndpointGeometry
      ((g.labelledResampledGraph T labels samples selector).deficient.restrict
        (g.singleTargetFilledVertices T labels samples selector r y)) R A L) :
    SourceFullEndpointGeometry
      ((g.labelledResampledGraph T labels samples selector).filledExteriorModel T
        (g.singleTargetOutsideVertices T labels samples selector r y)) R A L := by
  change SourceFullEndpointGeometry
    ((g.labelledResampledGraph T labels samples selector).deficient.restrict
      (filledExteriorVertices T (g.singleTargetOutsideVertices T labels samples selector r y))) R A L
  rw [g.singleTargetOutside_fill_eq]
  exact h

end RegularGraph
end LocalLaw
