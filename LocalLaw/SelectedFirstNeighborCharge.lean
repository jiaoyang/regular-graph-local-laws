import LocalLaw.OmittedLeafData
import LocalLaw.OmittedSwitchingSlots

/-! # New selected-B incidences are charged to actual old slots and A roots -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance selectedFirstNeighborChargeDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type}[Fintype V]{T : Set V}{ι : Type}[Fintype ι]

def ordinaryEmptyOldNeighborEmbedding (s : LabelledResamplingState V T ι)(selector : ℕ)
    (v : (Tᶜ : Set V)) : s.OmittedOrdinarySlot selector ∅ v ↪
      {b:s.selectedFirstSet selector // (outsideGraph s.graph T).Adj b.val v} where
  toFun i := ⟨⟨s.admissibleSampleVertex selector i.val,⟨i.val,rfl⟩⟩,i.property.2.1⟩
  inj' := by
    intro i j h
    exact Subtype.ext ((s.selectedFirstEmbedding selector).injective
      (congrArg (fun b:{b:s.selectedFirstSet selector // (outsideGraph s.graph T).Adj b.val v} => b.val.val) h))

def addedEmptyRootEquiv (s : LabelledResamplingState V T ι)(selector : ℕ)
    (v : (Tᶜ : Set V)) : s.OmittedAddedSlot selector ∅ v ≃
      {i:s.AdmissibleSampleIndex selector // v=s.admissibleBoundaryVertex selector i} where
  toFun i := ⟨i.val,i.property.2⟩
  invFun i := ⟨i.val,by simp,i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem selectedFirst_new_neighbor_count_le (s : LabelledResamplingState V T ι)(selector : ℕ)
    (v : (Tᶜ : Set V)) :
    Nat.card {b:s.selectedFirstSet selector // (outsideGraph (s.fullResample selector).graph T).Adj b.val v} ≤
      Nat.card {b:s.selectedFirstSet selector // (outsideGraph s.graph T).Adj b.val v}+
        Nat.card {i:s.AdmissibleSampleIndex selector // v=s.admissibleBoundaryVertex selector i} := by
  have hc := s.omitted_new_neighbor_count selector ∅ v
  simp only [Set.mem_empty_iff_false,not_false_eq_true,true_and] at hc
  rw [hc,Nat.card_congr (s.addedEmptyRootEquiv selector v)]
  exact Nat.add_le_add_right
    (Nat.card_le_card_of_injective _ (s.ordinaryEmptyOldNeighborEmbedding selector v).injective) _

end LabelledResamplingState
end LocalLaw
