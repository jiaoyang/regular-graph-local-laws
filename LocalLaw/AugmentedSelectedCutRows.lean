import LocalLaw.SelectedFirstRegionCharge

/-! # The actual old two-target region satisfies every cut-row support premise -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance augmentedSelectedCutRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type}[Fintype V]{T : Set V}{ι : Type}[Fintype ι]

omit [Fintype V] [Fintype ι] in
theorem admissibleBoundaryVertex_mem_twoTarget (s : LabelledResamplingState V T ι)
    (selector r : ℕ)(x y : (Tᶜ:Set V))(i : s.AdmissibleSampleIndex selector) :
    s.admissibleBoundaryVertex selector i ∈ s.twoTargetEndpointVertices selector r x y := by
  apply s.endpointModelVertices_subset_twoTargetEndpointVertices selector r x y
  exact ⟨s.admissibleBoundaryVertex selector i,Or.inl ⟨s.boundary i.val,rfl⟩,by
    change (outsideGraph s.graph T).edist (s.admissibleBoundaryVertex selector i)
      (s.admissibleBoundaryVertex selector i)≤(r:ℕ∞)
    rw [SimpleGraph.edist_self]
    exact bot_le⟩

def twoTargetBoundaryCommonVertex (s : LabelledResamplingState V T ι)(selector r : ℕ)
    (x y : (Tᶜ:Set V))(i : s.AdmissibleSampleIndex selector) :
    ((s.partialFirstRemovedSet selector (s.twoTargetEndpointVertices selector r x y))ᶜ:
      Set (s.twoTargetEndpointVertices selector r x y)) :=
  s.regionalBoundaryCommonVertex selector (s.twoTargetEndpointVertices selector r x y)
    (s.admissibleBoundaryVertex_mem_twoTarget selector r x y) i

theorem twoTarget_selectedFirst_new_cut_rows (s : LabelledResamplingState V T ι)
    (d selector r : ℕ)(x y : (Tᶜ:Set V))
    (a : ((s.partialFirstRemovedSet selector (s.twoTargetEndpointVertices selector r x y))ᶜ:
      Set (s.twoTargetEndpointVertices selector r x y))→ℂ) :
    let A := s.twoTargetEndpointVertices selector r x y
    let B := s.partialFirstRemovedSet selector A
    (∑b:B,‖∑v:(Bᶜ:Set A),a v*
      normalizedAdjacency ((outsideGraph (s.fullResample selector).graph T).induce A) d v.val b.val‖)≤
      (Real.sqrt ((d:ℝ)-1))⁻¹ *
        ((∑l:DeletedLeafIndex ((outsideGraph s.graph T).induce A) B,‖a l.1‖)+
          ∑i:s.AdmissibleSampleIndex selector,‖a (s.twoTargetBoundaryCommonVertex selector r x y i)‖) := by
  exact s.selectedFirst_region_new_cut_product_rows d selector _
    (s.selectedFirstSet_subset_twoTarget selector r x y)
    (s.admissibleBoundaryVertex_mem_twoTarget selector r x y) a

end LabelledResamplingState
end LocalLaw
