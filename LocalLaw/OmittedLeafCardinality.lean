import LocalLaw.OmittedLeafCounts
import LocalLaw.SelectedLeafCardinality

/-! # Every actual completed slot is charged to a boundary label -/

noncomputable section
namespace LocalLaw
local instance omittedLeafCardinalityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type}[Fintype V]{T : Set V}{ι : Type}[Fintype ι]

def omittedOldGlobalLeafEmbedding (s : LabelledResamplingState V T ι)(selector : ℕ)
    (S : Set (Tᶜ : Set V)) : s.OmittedOldLeaves selector S ↪
      DeletedLeafIndex (outsideGraph s.graph T) (s.selectedFirstSet selector) :=
  Function.Embedding.sigmaMap (Function.Embedding.subtype (fun v:((s.selectedFirstSet selector)ᶜ:Set (Tᶜ:Set V)) => v.val∈S))
    (fun _ => Function.Embedding.refl _)

end LabelledResamplingState
namespace RegularGraph
variable {N d : ℕ}{ι : Type}[Fintype ι]

theorem omittedAllLeaves_card_bound (g : RegularGraph N d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector : ℕ)(S : Set (Tᶜ : Set (Fin N))) :
    Nat.card ((g.admissibleState T labels samples).OmittedOldLeaves selector S ⊕
      (g.admissibleState T labels samples).OmittedExtraLeaves selector S) ≤
        (d+1)*Nat.card (BoundaryOrientedEdge g.graph T) := by
  let s := g.admissibleState T labels samples
  have hI : Nat.card (s.AdmissibleSampleIndex selector) ≤ Nat.card ι :=
    Finite.card_subtype_le (s.Eligible selector)
  have hW : Nat.card (s.selectedFirstSet selector) ≤ Nat.card ι :=
    (Finite.card_range_le (s.selectedFirstEmbedding selector)).trans hI
  have hOld : Nat.card (s.OmittedOldLeaves selector S) ≤ d*Nat.card ι :=
    (Nat.card_le_card_of_injective _ (s.omittedOldGlobalLeafEmbedding selector S).injective).trans
      ((deletedLeafIndex_card_bound (outsideGraph g.graph T) (s.selectedFirstSet selector) d
        (g.deficient.delete T).degree_le).trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left d hW))
  have hExtra : Nat.card (s.OmittedExtraLeaves selector S) ≤ Nat.card ι :=
    (Finite.card_subtype_le (fun i:s.AdmissibleSampleIndex selector =>
      s.admissibleSampleVertex selector i∉S ∧ s.admissibleBoundaryVertex selector i∈S)).trans hI
  rw [Nat.card_sum]
  calc
    _ ≤ d*Nat.card ι+Nat.card ι := Nat.add_le_add hOld hExtra
    _ = (d+1)*Nat.card (BoundaryOrientedEdge g.graph T) := by
      rw [Nat.card_congr labels]
      ring

end RegularGraph
end LocalLaw
