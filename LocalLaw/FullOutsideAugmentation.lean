import LocalLaw.FullOldTwoTargetGeometry
import LocalLaw.PartialInnerMasks
import LocalLaw.AugmentedPairCapture

/-! # Exact outside slice of a full two-target augmentation

A full path which passes through T exits at an original boundary root.
Those root balls are already in the fixed central exterior model. Thus,
for outside centers, the full and outside augmented sets have exactly the
same outside slice, even though their literal target pair balls may differ.
-/

noncomputable section
namespace LocalLaw
local instance fullOutsideAugmentationDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type}{T:Set V}{ι:Type}

theorem fullTwoTarget_eq_filled_outside (s:LabelledResamplingState V T ι)(selector r:ℕ)
    (x y:(Tᶜ:Set V)) :
    s.fullTwoTargetVertices selector r x.val y.val=
      filledExteriorVertices T (s.twoTargetEndpointVertices selector r x y) := by
  let K:=s.twoTargetEndpointVertices selector r x y
  have hb (a:BoundaryOrientedEdge s.graph T) :
      graphBallVertices (outsideGraph s.graph T) (boundaryOutsideVertex s.graph T a) r⊆K:=by
    intro v hv
    exact Or.inl ⟨boundaryOutsideVertex s.graph T a,Or.inl ⟨a,rfl⟩,hv⟩
  have hx : graphBallVertices s.graph x.val r⊆filledExteriorVertices T K :=
    filled_captures_outside_ball s.graph T K r hb x (fun v hv=>Or.inr (Or.inl hv))
  have hy : graphBallVertices s.graph y.val r⊆filledExteriorVertices T K :=
    filled_captures_outside_ball s.graph T K r hb y (fun v hv=>Or.inr (Or.inr hv))
  ext v
  constructor
  · rintro ((hv|⟨w,hw,rfl⟩)|hv|hv)
    · exact Or.inl hv
    · exact Or.inr ⟨w,Or.inl hw,rfl⟩
    · exact hx hv
    · exact hy hv
  · rintro (hv|⟨w,hw,rfl⟩)
    · exact Or.inl (Or.inl hv)
    · rcases hw with hw|hw|hw
      · exact Or.inl (Or.inr ⟨w,hw,rfl⟩)
      · exact Or.inr (Or.inl ((graphHom_edist_le
          (SimpleGraph.Embedding.induce (G:=s.graph) Tᶜ).toHom x w).trans hw))
      · exact Or.inr (Or.inr ((graphHom_edist_le
          (SimpleGraph.Embedding.induce (G:=s.graph) Tᶜ).toHom y w).trans hw))

theorem fullTwoTarget_outside_slice (s:LabelledResamplingState V T ι)(selector r:ℕ)
    (x y:(Tᶜ:Set V)) :
    s.fullSliceOutside (s.fullTwoTargetVertices selector r x.val y.val)=
      s.twoTargetEndpointVertices selector r x y := by
  ext v
  change v.val∈s.fullTwoTargetVertices selector r x.val y.val ↔ v∈s.twoTargetEndpointVertices selector r x y
  rw [s.fullTwoTarget_eq_filled_outside selector r x y]
  exact filledExterior_outside_mem T _ v

variable [Fintype ι]
theorem switched_full_pair_outside_subset (s:LabelledResamplingState V T ι)(selector r:ℕ)
    (x y:(Tᶜ:Set V)) :
    s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x.val y.val r) ⊆
      s.twoTargetEndpointVertices selector r x y := by
  intro v hv
  have hh:=s.switched_full_pair_subset_old_augmentation selector r x.val y.val hv
  rw [←s.fullTwoTarget_outside_slice selector r x y]
  exact hh

end LabelledResamplingState
end LocalLaw
