import LocalLaw.CanonicalBoundaryCore
import LocalLaw.OmittedLeafCounts
import LocalLaw.AttachedLeafSubfamilyRows

/-! # Every kept mate row is charged to old slots and retained A roots -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance omittedKeptMateRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type}[Fintype V]{T : Set V}{ι : Type}[Fintype ι]

def omittedExtraBoundaryEmbedding (s : LabelledResamplingState V T ι)(selector : ℕ)
    (S : Set (Tᶜ:Set V)) : s.OmittedExtraLeaves selector S ↪ s.partialBoundaryMask selector S where
  toFun i := ⟨i.val,i.property.2⟩
  inj' := by
    intro i j h
    exact Subtype.ext (congrArg (fun k:s.partialBoundaryMask selector S => k.val) h)

theorem omittedKept_mate_rows_of_old_boundary (s : LabelledResamplingState V T ι)(selector : ℕ)
    (S : Set (Tᶜ:Set V))(P : s.OmittedCore selector S → s.OmittedCore selector S → ℂ)
    (KM KA : ℝ)
    (hOld : ∀u,∑l:s.OmittedOldLeaves selector S,‖P u l.1‖≤KM)
    (hA : ∀u,∑i:s.partialBoundaryMask selector S,‖P u (s.canonicalBoundaryCoreEmbedding selector S i)‖≤KA)
    (u : s.OmittedCore selector S) :
    (∑l:s.OmittedOrdinaryLeaves selector S ⊕ s.OmittedExtraLeaves selector S,
      ‖P u (s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l))‖)≤KM+KA := by
  have ho := finite_norm_sum_embedding_le (s.omittedOrdinaryOldEmbedding selector S)
    (fun l:s.OmittedOldLeaves selector S => P u l.1)
  have ha := finite_norm_sum_embedding_le (s.omittedExtraBoundaryEmbedding selector S)
    (fun i:s.partialBoundaryMask selector S => P u (s.canonicalBoundaryCoreEmbedding selector S i))
  calc
    _ = (∑l:s.OmittedOrdinaryLeaves selector S,‖P u l.1‖)+
        ∑i:s.OmittedExtraLeaves selector S,
          ‖P u (s.canonicalBoundaryCoreEmbedding selector S (s.omittedExtraBoundaryEmbedding selector S i))‖ := by
      rw [Fintype.sum_sum_type]
      rfl
    _ ≤ (∑l:s.OmittedOldLeaves selector S,‖P u l.1‖)+
        ∑i:s.partialBoundaryMask selector S,‖P u (s.canonicalBoundaryCoreEmbedding selector S i)‖ := add_le_add ho ha
    _ ≤ KM+KA := add_le_add (hOld u) (hA u)

end LabelledResamplingState
end LocalLaw
