import LocalLaw.ActualPartialBInverseCaps
import LocalLaw.PrincipalSetTransport
import LocalLaw.PartialFirstDeletionCaps

/-! # Indexed sampled-block bounds on the literal omitted vertex set -/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance partialFirstRemovedRowsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type} [Fintype V] {T:Set V} {ι:Type} [Fintype ι]

theorem partialFirstEmbedding_range (s:LabelledResamplingState V T ι)(selector:ℕ)
    (S:Set (Tᶜ:Set V)) : Set.range (s.partialFirstEmbedding selector S)=s.partialFirstRemovedSet selector S := by
  ext v
  constructor
  · rintro ⟨b,rfl⟩
    exact ⟨b.val,rfl⟩
  · intro hv
    let φ:=s.partialFirstRemovalEquiv selector S
    let b:=φ.symm ⟨v,hv⟩
    refine ⟨b,?_⟩
    exact congrArg Subtype.val (φ.apply_symm_apply ⟨v,hv⟩)

theorem removed_first_inverse_caps_of_indexed (s:LabelledResamplingState V T ι)(selector:ℕ)
    (S:Set (Tᶜ:Set V))(G:Matrix S S ℂ)(C:ℝ)
    (hindexed:∀E:Set (s.partialFirstMask selector S),
      let U:=(G.submatrix (s.partialFirstEmbedding selector S) (s.partialFirstEmbedding selector S)).submatrix
        (Subtype.val:E→s.partialFirstMask selector S) (Subtype.val:E→s.partialFirstMask selector S)
      IsUnit U ∧ (∀i,∑j,‖U⁻¹ i j‖≤C) ∧ (∀j,∑i,‖U⁻¹ i j‖≤C))
    (W:Set S)(hW:W⊆s.partialFirstRemovedSet selector S) :
    let U:=G.submatrix (Subtype.val:W→S) (Subtype.val:W→S)
    IsUnit U ∧ (∀i,∑j,‖U⁻¹ i j‖≤C) ∧ (∀j,∑i,‖U⁻¹ i j‖≤C) := by
  let e:=s.partialFirstEmbedding selector S
  let E:Set (s.partialFirstMask selector S):={i |e i∈W}
  have he:(e:s.partialFirstMask selector S→S) '' E=W:=by
    ext v
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact hi
    · intro hv
      have hm:v∈Set.range e:=by
        rw [s.partialFirstEmbedding_range selector S]
        exact hW hv
      obtain ⟨i,rfl⟩:=hm
      exact ⟨i,hv,rfl⟩
  have hh:=hindexed E
  have hcaps:=embedded_principal_inverse_rows_cols G e E C hh.1 hh.2.1 hh.2.2
  exact principal_inverse_caps_set_congr G ((e:s.partialFirstMask selector S→S) '' E) W he C hcaps

end LabelledResamplingState
end LocalLaw
