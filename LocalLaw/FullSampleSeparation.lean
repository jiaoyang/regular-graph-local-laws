import LocalLaw.FullSampleTreeValues

/-! # Actual full-metric separation of accepted samples from the old core -/

noncomputable section
namespace LocalLaw
namespace LabelledResamplingState
variable {V:Type} {T:Set V} {ι:Type}

theorem admissiblePairRoots_mem_triple (s:LabelledResamplingState V T ι) (selector:ℕ)
    (i:s.AdmissibleSampleIndex selector) (c:(Tᶜ:Set V))
    (hc:c∈s.admissiblePairRoots selector i) :
    c∈outsideTriple s.graph T s.samples (s.boundary i.val) := by
  simp only [admissiblePairRoots,Set.mem_insert_iff,Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl
  · exact (outsideTriple_mem_iff _ _ _ _ _).mpr (Or.inr (Or.inl rfl))
  · exact (outsideTriple_mem_iff _ _ _ _ _).mpr (Or.inr (Or.inr rfl))

theorem admissiblePairRoots_ambient_far_core (s:LabelledResamplingState V T ι) (selector:ℕ)
    (hselector:1≤selector) (i:s.AdmissibleSampleIndex selector) (c:(Tᶜ:Set V))
    (hc:c∈s.admissiblePairRoots selector i) (x:V)
    (hx:x∈T∨∃α:BoundaryOrientedEdge s.graph T,x=(boundaryOuterEndpoint s.graph T α).val) :
    ((selector-1:ℕ):ℕ∞)<s.graph.edist c.val x := by
  have hguard:=s.admissiblePairRoots_far_boundary selector hselector i hc
  rcases hx with hx | ⟨α,rfl⟩
  · exact (ENat.coe_le_coe.mpr (Nat.le_add_right _ 1)).trans_lt
      (boundaryFarOutside_ambient_far_set s.graph T (selector-1) c hguard x hx)
  · exact boundaryFarOutside_ambient_far_boundary s.graph T (selector-1) c hguard α

theorem admissiblePairRoots_ambient_separated (s:LabelledResamplingState V T ι) (selector:ℕ)
    (hselector:1≤selector) (i j:s.AdmissibleSampleIndex selector) (hij:i≠j)
    (c e:(Tᶜ:Set V)) (hc:c∈s.admissiblePairRoots selector i) (he:e∈s.admissiblePairRoots selector j) :
    ((selector-1:ℕ):ℕ∞)<s.graph.edist c.val e.val := by
  have hguard:=s.admissiblePairRoots_far_boundary selector hselector i hc
  have hlabel:s.boundary j.val≠s.boundary i.val:=by
    intro h
    exact hij (Subtype.ext (s.boundary.injective h).symm)
  have hout:=i.property.2 (s.boundary j.val) hlabel c (s.admissiblePairRoots_mem_triple selector i c hc)
    e (s.admissiblePairRoots_mem_triple selector j e he)
  exact boundaryFarOutside_ambient_far_of_outside_far s.graph T (selector-1) c e hguard
    ((ENat.coe_le_coe.mpr (Nat.sub_le _ _)).trans_lt hout)

end LabelledResamplingState
end LocalLaw
