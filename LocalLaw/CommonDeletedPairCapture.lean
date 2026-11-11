import LocalLaw.SelectedFirstDeletion
import LocalLaw.AugmentedPairCapture

/-! # Both comparison models capture the same physically deleted pair ball

Removing every accepted sampled first endpoint erases the complete outside
surgery. A path avoiding those endpoints is consequently a path in either
physical graph. Its radius-r pair ball is captured by the new pair model and
by the old two-target augmented model. The source deficient models themselves
agree after this full deletion, by actual saturation and lost-neighbor counts.
-/

noncomputable section
namespace LocalLaw
local instance commonDeletedCaptureDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type} [Fintype ι]

theorem common_deleted_pairBall_subset_new_pair (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (x y : ((s.selectedFirstSet selector)ᶜ : Set (Tᶜ : Set V))) :
    pairBallVertices ((outsideGraph s.graph T).induce (s.selectedFirstSet selector)ᶜ) x y r ⊆
      {v : ((s.selectedFirstSet selector)ᶜ : Set (Tᶜ : Set V)) |
        v.val ∈ pairBallVertices (outsideGraph (s.fullResample selector).graph T) x.val y.val r} := by
  intro v hv
  rw [←s.fullResample_outside_delete_selectedFirst_graph selector] at hv
  rcases hv with hx | hy
  · exact Or.inl ((ambient_edist_le_induced_edist
      (outsideGraph (s.fullResample selector).graph T) (s.selectedFirstSet selector)ᶜ x v).trans hx)
  · exact Or.inr ((ambient_edist_le_induced_edist
      (outsideGraph (s.fullResample selector).graph T) (s.selectedFirstSet selector)ᶜ y v).trans hy)

theorem common_deleted_pairBall_subset_old_augmentation (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (x y : ((s.selectedFirstSet selector)ᶜ : Set (Tᶜ : Set V))) :
    pairBallVertices ((outsideGraph s.graph T).induce (s.selectedFirstSet selector)ᶜ) x y r ⊆
      {v : ((s.selectedFirstSet selector)ᶜ : Set (Tᶜ : Set V)) |
        v.val ∈ s.twoTargetEndpointVertices selector r x.val y.val} := by
  intro v hv
  exact s.switched_pairBall_subset_old_augmentation selector r x.val y.val
    (s.common_deleted_pairBall_subset_new_pair selector r x y hv)

end LabelledResamplingState

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

/-- Full common-deleted source model equality also identifies every literal
restriction and its genuine inverse. No reference-class premise is needed. -/
theorem labelledResampled_common_deleted_restriction_eq (g : RegularGraph N d)
    (T : Set (Fin N)) (labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector : ℕ)
    (S : Set (((g.admissibleState T labels samples).selectedFirstSet selector)ᶜ :
      Set (Tᶜ : Set (Fin N)))) (q z : ℂ) :
    let W := (g.admissibleState T labels samples).selectedFirstSet selector
    (((g.labelledResampledGraph T labels samples selector).deficient.delete T).delete W).restrict S =
      (((g.deficient.delete T).delete W).restrict S) ∧
    ((((g.labelledResampledGraph T labels samples selector).deficient.delete T).delete W).restrict S).extensionGreen q z =
      (((g.deficient.delete T).delete W).restrict S).extensionGreen q z := by
  dsimp only
  rw [g.labelledResampled_delete_selectedFirst_eq T labels samples selector]
  exact ⟨rfl,rfl⟩

end RegularGraph
end LocalLaw
