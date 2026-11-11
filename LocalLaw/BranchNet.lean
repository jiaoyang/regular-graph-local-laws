import Mathlib

/-!
# Finite nets respecting a discontinuous error branch

Partition the spectral region into finitely many small cells, and select one
representative for each inhabited (cell, error-branch) pair. A target point is
then compared only with a representative in the same error branch. The number
of representatives is bounded by the number of cells times branches, even
when the branch classifier is discontinuous.
-/

open scoped BigOperators

namespace LocalLaw

section
variable {Z I J : Type*} [PseudoMetricSpace Z] [Nonempty Z]
variable [Fintype I] [Fintype J]

/-- A branch-preserving net with an explicit cardinality budget. -/
structure BranchNet (D : Set Z) (classify : Z → J) (h : ℝ) (K : ℕ) where
  centers : Finset Z
  in_domain : ∀ w ∈ centers, w ∈ D
  cardinality : centers.card ≤ K
  cover : ∀ z ∈ D, ∃ w ∈ centers, classify w = classify z ∧ dist z w ≤ h

/-- One representative per inhabited cell and branch suffices. No regularity
of the branch classifier is assumed. -/
theorem exists_branchNet (D : Set Z) (cell : Z → I) (classify : Z → J) (h : ℝ)
    (diameter : ∀ z ∈ D, ∀ w ∈ D, cell z = cell w → dist z w ≤ h) :
    Nonempty (BranchNet D classify h (Fintype.card I * Fintype.card J)) := by
  classical
  let inhabited : I × J → Prop := fun p => ∃ z ∈ D, cell z = p.1 ∧ classify z = p.2
  let active : Finset (I × J) := Finset.univ.filter inhabited
  let representative : I × J → Z := fun p =>
    if hp : inhabited p then Classical.choose hp else Classical.choice inferInstance
  have hrepresentative : ∀ p, inhabited p → representative p ∈ D ∧
      cell (representative p) = p.1 ∧ classify (representative p) = p.2 := by
    intro p hp
    dsimp [representative]
    rw [dif_pos hp]
    exact Classical.choose_spec hp
  let centers : Finset Z := active.image representative
  refine ⟨⟨centers, ?_, ?_, ?_⟩⟩
  · intro w hw
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
    exact (hrepresentative p (Finset.mem_filter.mp hp).2).1
  · calc
      centers.card ≤ active.card := Finset.card_image_le
      _ ≤ (Finset.univ : Finset (I × J)).card := Finset.card_filter_le _ _
      _ = Fintype.card I * Fintype.card J := by simp
  · intro z hz
    let p : I × J := (cell z, classify z)
    have hp : inhabited p := ⟨z, hz, rfl, rfl⟩
    have hactive : p ∈ active := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
    have hr := hrepresentative p hp
    refine ⟨representative p, Finset.mem_image.mpr ⟨p, hactive, rfl⟩, hr.2.2, ?_⟩
    exact diameter z hz (representative p) hr.1 hr.2.1.symm

end

end LocalLaw
