import LocalLaw.EndpointModelInvariance
import LocalLaw.ResamplingBoundaryLabels

/-! # Actual endpoint root sets are invariant under the full labelled switch -/

noncomputable section
namespace LocalLaw
local instance endpointRootInvarianceDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type*} {T : Set V} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem endpointModelRoots_mem_iff_quad (s : LabelledResamplingState V T ι) (selector : ℕ)
    (x : (Tᶜ : Set V)) :
    x∈s.endpointModelRoots selector ↔ ∃ j,
      x.val=(s.quad j).b ∨ (s.Eligible selector j ∧ (x.val=(s.quad j).c ∨ x.val=(s.quad j).d)) := by
  constructor
  · rintro (⟨α,hα⟩ | hx)
    · obtain ⟨j,rfl⟩ := s.boundary.surjective α
      exact ⟨j,Or.inl (congrArg Subtype.val hα.symm)⟩
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
      simp only [admissiblePairRoots,Set.mem_insert_iff,Set.mem_singleton_iff] at hi
      exact ⟨i.val,Or.inr ⟨i.property,hi.elim
        (fun h => Or.inl (congrArg Subtype.val h)) (fun h => Or.inr (congrArg Subtype.val h))⟩⟩
  · rintro ⟨j,hj | ⟨hj,hx | hx⟩⟩
    · exact Or.inl ⟨s.boundary j,Subtype.ext hj.symm⟩
    · apply Or.inr
      apply Set.mem_iUnion.mpr
      refine ⟨⟨j,hj⟩,?_⟩
      exact Or.inl (Subtype.ext hx)
    · apply Or.inr
      apply Set.mem_iUnion.mpr
      refine ⟨⟨j,hj⟩,?_⟩
      exact Or.inr (Subtype.ext hx)

theorem endpointModelRoots_resample (s : LabelledResamplingState V T ι) (selector : ℕ) :
    (s.fullResample selector).endpointModelRoots selector=s.endpointModelRoots selector := by
  ext x
  rw [(s.fullResample selector).endpointModelRoots_mem_iff_quad,s.endpointModelRoots_mem_iff_quad]
  apply exists_congr
  intro j
  rw [s.fullResample_eligible,s.fullResample_quad_at_label]
  by_cases hj : s.Eligible selector j
  · simp only [if_pos hj,hj,true_and,SwitchingQuad.inverse]
    tauto
  · simp only [if_neg hj,hj,if_false,false_and,or_false]

theorem endpointModelVertices_resample (s : LabelledResamplingState V T ι) (selector r : ℕ) :
    (s.fullResample selector).endpointModelVertices selector r=s.endpointModelVertices selector r := by
  unfold endpointModelVertices
  rw [s.endpointModelRoots_resample]
  exact (s.endpointModelVertices_fullResample selector r).symm

end LabelledResamplingState
end LocalLaw
