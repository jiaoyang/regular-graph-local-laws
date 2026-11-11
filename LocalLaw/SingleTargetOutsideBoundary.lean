import LocalLaw.DetachedBranchTarget
import LocalLaw.FilledEndpointLocality

/-! Canonical old-label coordinates in the actual one-target outside model. -/
noncomputable section
namespace LocalLaw
local instance singleTargetOutsideBoundaryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

def singleTargetOutsideBoundaryVertex (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (y : Fin N) (i : ι) : g.singleTargetOutsideVertices T labels samples selector r y :=
  (g.labelledResampledGraph T labels samples selector).filledBoundaryVertex T
    (g.singleTargetOutsideVertices T labels samples selector r y)
    (g.singleTargetOutside_boundary_capture T labels samples selector r y)
    (((g.admissibleState T labels samples).fullResample selector).boundary i)

theorem singleTargetOutsideBoundaryVertex_val (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (y : Fin N) (i : ι) :
    (g.singleTargetOutsideBoundaryVertex T labels samples selector r y i).val=
      ((g.admissibleState T labels samples).endpointFinalBoundaryRoot selector i).val :=
  ((g.admissibleState T labels samples).endpointFinalBoundaryRoot_outer selector i).symm

theorem singleTargetOutsideBoundaryVertex_tip (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (y : Fin N)
    (i : (g.admissibleState T labels samples).AdmissibleSampleIndex selector) :
    (g.singleTargetOutsideBoundaryVertex T labels samples selector r y i.val).val=
      (g.admissibleState T labels samples).admissibleSecondVertex selector i := by
  rw [g.singleTargetOutsideBoundaryVertex_val]
  simp only [LabelledResamplingState.endpointFinalBoundaryRoot,dif_pos i.property]
  rfl

theorem singleTargetOutsideBoundaryVertex_capture (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (y : Fin N) (hy : y∉T) (i : ι) :
    graphBallVertices (outsideGraph (g.labelledResampledGraph T labels samples selector).graph T)
      (g.singleTargetOutsideBoundaryVertex T labels samples selector r y i).val r⊆
        g.singleTargetOutsideVertices T labels samples selector r y := by
  intro v hv
  rw [g.singleTargetOutsideVertices_eq_union T labels samples selector r y hy]
  apply Or.inl
  exact (g.admissibleState T labels samples).endpointModel_contains_new_boundary_ball selector r
    (((g.admissibleState T labels samples).fullResample selector).boundary i) hv

theorem singleTargetOutsideTargetVertex_capture (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (y : Fin N) (hy : y∉T) :
    graphBallVertices (outsideGraph (g.labelledResampledGraph T labels samples selector).graph T)
      (g.singleTargetOutsideTargetVertex T labels samples selector r y hy).val r⊆
        g.singleTargetOutsideVertices T labels samples selector r y := by
  intro v hv
  rw [g.singleTargetOutsideVertices_eq_union T labels samples selector r y hy]
  exact Or.inr hv

end RegularGraph
end LocalLaw
