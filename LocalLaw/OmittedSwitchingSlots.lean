import LocalLaw.PartialSwitchRows
import LocalLaw.SelectedFirstDeletion

/-! # Actual omitted switching slots: ordinary old edges and new A edges

Every omitted sampled first vertex keeps all old neighbors except its C
tip, and gains its A neighbor. The two classes are disjoint because the
new A-B edge was absent before the admissible switch. Ordinary omitted
neighbors are retained explicitly; they are not silently charged only at A.
-/

noncomputable section
namespace LocalLaw
local instance omittedSwitchingSlotsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type}{T:Set V}{ι:Type}[Fintype ι]

def OmittedNewIncident (s:LabelledResamplingState V T ι)(selector:ℕ)
    (S:Set (Tᶜ:Set V))(v:(Tᶜ:Set V)) :=
  {i:s.AdmissibleSampleIndex selector //s.admissibleSampleVertex selector i∉S ∧
    (outsideGraph (s.fullResample selector).graph T).Adj (s.admissibleSampleVertex selector i) v}

def OmittedOrdinarySlot (s:LabelledResamplingState V T ι)(selector:ℕ)
    (S:Set (Tᶜ:Set V))(v:(Tᶜ:Set V)) :=
  {i:s.AdmissibleSampleIndex selector //s.admissibleSampleVertex selector i∉S ∧
    (outsideGraph s.graph T).Adj (s.admissibleSampleVertex selector i) v ∧
      v≠s.admissibleSecondVertex selector i}

def OmittedAddedSlot (s:LabelledResamplingState V T ι)(selector:ℕ)
    (S:Set (Tᶜ:Set V))(v:(Tᶜ:Set V)) :=
  {i:s.AdmissibleSampleIndex selector //s.admissibleSampleVertex selector i∉S ∧
    v=s.admissibleBoundaryVertex selector i}

instance omittedOrdinarySlotFintype (s:LabelledResamplingState V T ι)(selector:ℕ)
    (S:Set (Tᶜ:Set V))(v:(Tᶜ:Set V)) : Fintype (s.OmittedOrdinarySlot selector S v) := by
  unfold OmittedOrdinarySlot
  infer_instance

instance omittedAddedSlotFintype (s:LabelledResamplingState V T ι)(selector:ℕ)
    (S:Set (Tᶜ:Set V))(v:(Tᶜ:Set V)) : Fintype (s.OmittedAddedSlot selector S v) := by
  unfold OmittedAddedSlot
  infer_instance

omit [Fintype ι] in
theorem omittedOrdinary_ne_added (s:LabelledResamplingState V T ι)(selector:ℕ)
    (i:s.AdmissibleSampleIndex selector)(v:(Tᶜ:Set V))
    (h:(outsideGraph s.graph T).Adj (s.admissibleSampleVertex selector i) v) :
    v≠s.admissibleBoundaryVertex selector i := by
  intro hv
  have hi:=sampledSwitching_admissible s.graph T selector s.samples (s.boundary i.val)
    i.property.1 i.property.2
  rw [hv] at h
  exact hi.new_bc h.symm

def omittedNewIncidentEquiv (s:LabelledResamplingState V T ι)(selector:ℕ)
    (S:Set (Tᶜ:Set V))(v:(Tᶜ:Set V)) :
    s.OmittedNewIncident selector S v≃
      s.OmittedOrdinarySlot selector S v⊕s.OmittedAddedSlot selector S v where
  toFun e:=if hv:v=s.admissibleBoundaryVertex selector e.val then .inr ⟨e.val,e.property.1,hv⟩
    else .inl ⟨e.val,e.property.1,((s.fullResample_outside_first_row selector e.val v).mp e.property.2).resolve_right hv⟩
  invFun e:=match e with
    | .inl e=>⟨e.val,e.property.1,(s.fullResample_outside_first_row selector e.val v).mpr (Or.inl e.property.2)⟩
    | .inr e=>⟨e.val,e.property.1,(s.fullResample_outside_first_row selector e.val v).mpr (Or.inr e.property.2)⟩
  left_inv e:=by
    by_cases hv:v=s.admissibleBoundaryVertex selector e.val
    · simp only [dif_pos hv]
      rfl
    · simp only [dif_neg hv]
      rfl
  right_inv e:=by
    rcases e with e | e
    · simp only [dif_neg (s.omittedOrdinary_ne_added selector e.val v e.property.2.1)]
      rfl
    · simp only [dif_pos e.property.2]
      rfl

def omittedNewNeighborEquiv (s:LabelledResamplingState V T ι)(selector:ℕ)
    (S:Set (Tᶜ:Set V))(v:(Tᶜ:Set V)) :
    s.OmittedNewIncident selector S v≃
      {b:s.selectedFirstSet selector //b.val∉S ∧
        (outsideGraph (s.fullResample selector).graph T).Adj b.val v} :=
  Equiv.ofBijective (fun e=>⟨⟨s.admissibleSampleVertex selector e.val,⟨e.val,rfl⟩⟩,e.property⟩) (by
    constructor
    · intro e f h
      apply Subtype.ext
      apply (s.selectedFirstEmbedding selector).injective
      exact congrArg (fun a:{b:s.selectedFirstSet selector //b.val∉S ∧
        (outsideGraph (s.fullResample selector).graph T).Adj b.val v}=>a.val.val) h
    · intro b
      obtain ⟨i,hi⟩:=b.val.property
      have hm:s.admissibleSampleVertex selector i∉S ∧
          (outsideGraph (s.fullResample selector).graph T).Adj (s.admissibleSampleVertex selector i) v :=by
        rw [show s.admissibleSampleVertex selector i=b.val.val from hi]
        exact b.property
      exact ⟨⟨i,hm⟩,Subtype.ext (Subtype.ext hi)⟩)

theorem omitted_new_neighbor_count (s:LabelledResamplingState V T ι)(selector:ℕ)
    (S:Set (Tᶜ:Set V))(v:(Tᶜ:Set V)) :
    Nat.card {b:s.selectedFirstSet selector //b.val∉S ∧
      (outsideGraph (s.fullResample selector).graph T).Adj b.val v}=
      Nat.card (s.OmittedOrdinarySlot selector S v)+Nat.card (s.OmittedAddedSlot selector S v) := by
  rw [←Nat.card_congr (s.omittedNewNeighborEquiv selector S v),
    Nat.card_congr (s.omittedNewIncidentEquiv selector S v),Nat.card_sum]

end LabelledResamplingState
end LocalLaw
