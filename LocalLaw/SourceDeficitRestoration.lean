import LocalLaw.BoundaryDeficitFibers
import LocalLaw.SourceResamplingStructural
import LocalLaw.AdmissibleGreenBlock

/-!
# Literal inherited deficit restoration under the full source resampling

Outside deficit equals its actual boundary-label fiber. The exact label swap
therefore restores old attachment units and adds precisely the detached-tip
units. No deficit transformation is assumed from a graph picture.
-/

noncomputable section
namespace LocalLaw
local instance sourceDeficitRestorationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace LabelledResamplingState
variable {V : Type*} {T : Set V} {ι : Type*}

def restoredBoundaryLabels [Fintype ι] (s : LabelledResamplingState V T ι) (selector : ℕ)
    (v : (Tᶜ : Set V)) : ℕ := Nat.card {i : ι // s.Eligible selector i ∧ (s.boundary i).val.2 = v.val}

def detachedBoundaryLabels [Fintype ι] (s : LabelledResamplingState V T ι) (selector : ℕ)
    (v : (Tᶜ : Set V)) : ℕ := Nat.card {i : ι // s.Eligible selector i ∧ (s.samples (s.boundary i)).val.2 = v.val}

theorem detachedBoundaryLabels_eq_zero [Fintype ι] (s : LabelledResamplingState V T ι)
    (selector : ℕ) (v : (Tᶜ : Set V))
    (haway : ∀ i, s.Eligible selector i → (s.samples (s.boundary i)).val.2 ≠ v.val) :
    s.detachedBoundaryLabels selector v = 0 := by
  letI : IsEmpty {i : ι // s.Eligible selector i ∧ (s.samples (s.boundary i)).val.2 = v.val} :=
    ⟨fun i => haway i.val i.property.1 i.property.2⟩
  exact Nat.card_of_isEmpty

theorem restoredBoundaryLabels_eq_zero [Fintype ι] (s : LabelledResamplingState V T ι)
    (selector : ℕ) (v : (Tᶜ : Set V))
    (haway : ∀ i, s.Eligible selector i → (s.boundary i).val.2 ≠ v.val) :
    s.restoredBoundaryLabels selector v = 0 := by
  letI : IsEmpty {i : ι // s.Eligible selector i ∧ (s.boundary i).val.2 = v.val} :=
    ⟨fun i => haway i.val i.property.1 i.property.2⟩
  exact Nat.card_of_isEmpty

theorem restoredBoundaryLabels_positive [Fintype ι] (s : LabelledResamplingState V T ι)
    (selector : ℕ) (i : ι) (hi : s.Eligible selector i) :
    1 ≤ s.restoredBoundaryLabels selector (boundaryOutsideVertex s.graph T (s.boundary i)) := by
  letI : Nonempty {j : ι // s.Eligible selector j ∧ (s.boundary j).val.2 = (s.boundary i).val.2} :=
    ⟨⟨i, hi, rfl⟩⟩
  have hh : 0 < Nat.card {j : ι // s.Eligible selector j ∧ (s.boundary j).val.2 = (s.boundary i).val.2} := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_pos
  exact Nat.succ_le_of_lt hh

end LabelledResamplingState

namespace RegularGraph
variable {N d : ℕ} {ι : Type*} [Fintype ι]

theorem labelledResampled_deleted_deficit_conservation (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector : ℕ) (v : (Tᶜ : Set (Fin N))) :
    let s : LabelledResamplingState (Fin N) T ι := ⟨g.graph, boundary, S⟩
    ((g.labelledResampledGraph T boundary S selector).deficient.delete T).deficit v +
        s.restoredBoundaryLabels selector v =
      (g.deficient.delete T).deficit v + s.detachedBoundaryLabels selector v := by
  let s : LabelledResamplingState (Fin N) T ι := ⟨g.graph, boundary, S⟩
  let gnew := g.labelledResampledGraph T boundary S selector
  have hOld := Nat.card_congr (s.boundaryNeighborLabelEquiv v)
  have hNew := Nat.card_congr ((s.fullResample selector).boundaryNeighborLabelEquiv v)
  have hswap := s.fullResample_boundary_fiber_conservation selector v
  rw [← hOld, ← hNew] at hswap
  rw [g.deficient.delete_deficit_eq_removed_neighbors,
    gnew.deficient.delete_deficit_eq_removed_neighbors]
  dsimp only [deficient]
  simpa only [Nat.zero_add] using hswap

/-- Central and b-side vertices have no detached-tip addition, so their
new deficit plus the restored attachment count equals the old deficit. -/
theorem labelledResampled_deleted_deficit_restoration (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector : ℕ) (v : (Tᶜ : Set (Fin N)))
    (haway : ∀ i, (g.admissibleState T boundary S).Eligible selector i → (S (boundary i)).val.2 ≠ v.val) :
    let s := g.admissibleState T boundary S
    ((g.labelledResampledGraph T boundary S selector).deficient.delete T).deficit v +
        s.restoredBoundaryLabels selector v = (g.deficient.delete T).deficit v := by
  have hh := g.labelledResampled_deleted_deficit_conservation T boundary S selector v
  dsimp only at hh ⊢
  have hzero := (g.admissibleState T boundary S).detachedBoundaryLabels_eq_zero selector v haway
  dsimp only [admissibleState] at hzero ⊢
  rw [hzero, add_zero] at hh
  exact hh

end RegularGraph
end LocalLaw
