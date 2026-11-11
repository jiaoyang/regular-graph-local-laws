import LocalLaw.DetachedEndpointModel
import LocalLaw.AdmissibleEndpointModel

/-! # Actual restoration hypotheses for the endpoint component budget -/

noncomputable section
namespace LocalLaw
local instance endpointRestorationInputsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type*} [Fintype ι]

theorem endpoint_core_deficit_restoration (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector)
    (v : (g.admissibleState T boundary S).endpointModelVertices selector r)
    (hv : v.val ∈ (g.admissibleState T boundary S).centralEndpointPatch r) :
    (g.switchedEndpointModel T boundary S selector r).deficit v +
        (g.admissibleState T boundary S).restoredBoundaryLabels selector v.val =
      (g.endpointModel T boundary S selector r).deficit v := by
  let s := g.admissibleState T boundary S
  have h := g.labelledResampled_deleted_deficit_conservation T boundary S selector v.val
  dsimp only at h
  have hz := s.detachedBoundaryLabels_zero_on_central selector r hsep v.val hv
  change _ + s.restoredBoundaryLabels selector v.val = _ + s.detachedBoundaryLabels selector v.val at h
  rw [hz, add_zero] at h
  exact h

theorem endpoint_B_deficit_zero (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector)
    (i : (g.admissibleState T boundary S).AdmissibleSampleIndex selector)
    (v : (g.admissibleState T boundary S).endpointModelVertices selector r)
    (hv : v.val ∈ (g.admissibleState T boundary S).sampledFirstBranch selector r i) :
    (g.switchedEndpointModel T boundary S selector r).deficit v = 0 :=
  g.endpoint_B_zero_deficit T boundary S selector r hsep i v.val hv

theorem endpoint_C_deficit_one_root (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector)
    (i : (g.admissibleState T boundary S).AdmissibleSampleIndex selector)
    (v : (g.admissibleState T boundary S).endpointModelVertices selector r)
    (hv : v.val ∈ (g.admissibleState T boundary S).sampledSecondBranch selector r i) :
    (g.switchedEndpointModel T boundary S selector r).deficit v =
      if v = (g.admissibleState T boundary S).endpointTipVertex selector r i then 1 else 0 := by
  let s := g.admissibleState T boundary S
  have h := g.endpoint_C_one_root_deficit T boundary S selector r hsep i v.val hv
  by_cases he : v = s.endpointTipVertex selector r i
  · rw [if_pos he]
    have he' : v.val = s.admissibleSecondVertex selector i := congrArg Subtype.val he
    rw [if_pos he'] at h
    exact h
  · rw [if_neg he]
    have he' : v.val ≠ s.admissibleSecondVertex selector i := fun h => he (Subtype.ext h)
    rw [if_neg he'] at h
    exact h

theorem endpoint_attach_restored_positive (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (i : (g.admissibleState T boundary S).AdmissibleSampleIndex selector) :
    1 ≤ (g.admissibleState T boundary S).restoredBoundaryLabels selector
      ((g.admissibleState T boundary S).endpointAttachmentVertex selector r i).val :=
  (g.admissibleState T boundary S).restoredBoundaryLabels_positive selector i.val i.property

end RegularGraph
end LocalLaw
