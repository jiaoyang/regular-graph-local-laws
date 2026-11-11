import LocalLaw.SelectedCommonShiftedCapture

/-! # Mixed-center and zero-radius common-deleted captures -/

noncomputable section
namespace LocalLaw
namespace LabelledResamplingState
variable {V:Type}{T:Set V}{ι:Type}[Fintype ι]

theorem selectedCommon_mixed_shifted_capture (s:LabelledResamplingState V T ι)(selector r ri:ℕ)
    (hri:ri≤r)(A:Set (Tᶜ:Set V))(x y:(Tᶜ:Set V))
    (u:((s.partialFirstRemovedSet selector A)ᶜ:Set A))
    (hS:u.val.val∈pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r)
    (hu:ri=0 ∨ (outsideGraph (s.fullResample selector).graph T).edist x u.val.val≤((r-ri:ℕ):ℕ∞) ∨
      (outsideGraph (s.fullResample selector).graph T).edist y u.val.val≤((r-ri:ℕ):ℕ∞)) :
    graphBallVertices (outsideGraph ((outsideGraph s.graph T).induce A)
      (s.partialFirstRemovedSet selector A)) u ri ⊆
        {v:((s.partialFirstRemovedSet selector A)ᶜ:Set A) |
          v.val.val∈pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r} := by
  rcases hu with hzero|hu|hu
  · subst ri
    intro v hv
    have he:u=v:=SimpleGraph.edist_eq_zero_iff.mp (le_antisymm hv bot_le)
    exact he ▸ hS
  · exact s.selectedCommon_left_shifted_capture selector r ri hri A x y u hu
  · exact s.selectedCommon_right_shifted_capture selector r ri hri A x y u hu

end LabelledResamplingState
end LocalLaw
