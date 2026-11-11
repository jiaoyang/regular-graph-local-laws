import LocalLaw.OmittedLeafData
import LocalLaw.EligibleCentralIsolation

/-! # Retained eligible A roots in the literal global-deleted local core -/

noncomputable section
namespace LocalLaw
local instance canonicalBoundaryCoreDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type}[Fintype V]{T : Set V}{ι : Type}[Fintype ι]

def canonicalBoundaryCoreEmbedding (s : LabelledResamplingState V T ι)(selector : ℕ)
    (S : Set (Tᶜ:Set V)) : s.partialBoundaryMask selector S ↪ s.OmittedCore selector S where
  toFun i := ⟨⟨s.admissibleBoundaryVertex selector i.val,
    s.admissibleBoundaryVertex_not_selectedFirst selector i.val⟩,i.property⟩
  inj' := by
    intro i j h
    exact Subtype.ext (s.admissibleBoundaryVertex_injective selector
      (congrArg (fun v:s.OmittedCore selector S => v.val.val) h))

omit [Fintype V] [Fintype ι] in
theorem canonicalBoundaryCoreEmbedding_separated (s : LabelledResamplingState V T ι)
    (selector : ℕ)(S : Set (Tᶜ:Set V))(i j : s.partialBoundaryMask selector S)(hne : i≠j) :
    (selector:ℕ∞)<(((outsideGraph s.graph T).induce (s.selectedFirstSet selector)ᶜ).induce
      {v | v.val∈S}).edist (s.canonicalBoundaryCoreEmbedding selector S i) (s.canonicalBoundaryCoreEmbedding selector S j) := by
  have hβ : s.boundary j.val.val≠s.boundary i.val.val := fun h =>
    hne (Subtype.ext (Subtype.ext (s.boundary.injective h).symm))
  have hf := s.eligible_boundary_root_far selector i.val (s.boundary j.val.val) hβ
  let f : (((outsideGraph s.graph T).induce (s.selectedFirstSet selector)ᶜ).induce {v | v.val∈S}) →g
      outsideGraph s.graph T := ⟨fun v => v.val.val,fun h => h⟩
  exact hf.trans_le (graphHom_edist_le f _ _)

omit [Fintype V] in
theorem canonicalBoundaryMask_card (s : LabelledResamplingState V T ι)(selector : ℕ)
    (S : Set (Tᶜ:Set V)) : Nat.card (s.partialBoundaryMask selector S)≤Nat.card (BoundaryOrientedEdge s.graph T) := by
  have hh := (Finite.card_subtype_le (fun i:s.AdmissibleSampleIndex selector =>
    s.admissibleBoundaryVertex selector i∈S)).trans (Finite.card_subtype_le (s.Eligible selector))
  exact hh.trans_eq (Nat.card_congr s.boundary)

end LabelledResamplingState
end LocalLaw
