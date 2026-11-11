import LocalLaw.SingleTargetOutsideModel

/-! # The outside one-target model is exactly an outside-metric augmentation -/

noncomputable section
namespace LocalLaw
local instance singleTargetOutsideLocalityDecidable (p:Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ} {ι:Type} [Fintype ι]

theorem singleTargetOutsideVertices_eq_union (g:RegularGraph N d) (T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector r:ℕ) (y:Fin N) (hy:y∉T) :
    g.singleTargetOutsideVertices T labels samples selector r y=
      (g.admissibleState T labels samples).endpointModelVertices selector r ∪
        graphBallVertices (outsideGraph (g.labelledResampledGraph T labels samples selector).graph T) ⟨y,hy⟩ r := by
  let s:=g.admissibleState T labels samples
  let G:=(g.labelledResampledGraph T labels samples selector).graph
  ext v
  constructor
  · intro hv
    change v.val∈filledExteriorVertices T (s.endpointModelVertices selector r) ∨
      (v.val∈graphBallVertices G y r ∨ v.val∈graphBallVertices G y r) at hv
    rcases hv with hv | hv
    · exact Or.inl ((filledExterior_outside_mem T (s.endpointModelVertices selector r) v).mp hv)
    · have hvB:=hv.elim id id
      obtain ⟨p,hp⟩:=graphBall_exists_walk_length_le G y v.val r hvB
      rcases walk_outside_or_last_exit G T p v.property with ⟨hy',q,hq⟩ | ⟨α,pref,q,hlen⟩
      · exact Or.inr ((SimpleGraph.edist_le q).trans (ENat.coe_le_coe.mpr (hq.trans_le hp)))
      · exact Or.inl (s.endpointModel_contains_new_boundary_ball selector r α
          ((SimpleGraph.edist_le q).trans (ENat.coe_le_coe.mpr (by omega : q.length≤r))))
  · rintro (hv | hv)
    · exact Or.inl (Or.inr ⟨v,hv,rfl⟩)
    · exact Or.inr (Or.inl ((graphHom_edist_le (SimpleGraph.Embedding.induce (G:=G) Tᶜ).toHom
        ⟨y,hy⟩ v).trans hv))

end RegularGraph
end LocalLaw
