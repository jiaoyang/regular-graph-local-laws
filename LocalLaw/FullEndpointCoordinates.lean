import LocalLaw.FullEndpointMasks

/-! # The canonical full masks give the literal full-quad precision update -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance actualFullQuadCouplingDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} [Fintype V] {T : Set V} {ι : Type} [Fintype ι]

omit [Fintype V] [Fintype ι] in
theorem fullCore_ne_inner_sample (s : LabelledResamplingState V T ι)
    (selector : ℕ) (S : Set V) (k : s.fullCoreMask S) (i : s.AdmissibleSampleIndex selector) :
    k.val ≠ (s.admissibleSampleVertex selector i).val :=
  fun h => s.admissibleFirst_not_fullCore selector i (h ▸ k.property.2)

omit [Fintype V] [Fintype ι] in
theorem fullCore_ne_second_sample (s : LabelledResamplingState V T ι)
    (selector : ℕ) (hs : 1 ≤ selector) (S : Set V) (k : s.fullCoreMask S)
    (i : s.AdmissibleSampleIndex selector) :
    k.val ≠ (s.admissibleSecondVertex selector i).val :=
  fun h => s.admissibleSecond_not_fullCore selector hs i (h ▸ k.property.2)

omit [Fintype V] [Fintype ι] in
theorem full_first_inner_ne (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i j : s.AdmissibleSampleIndex selector) :
    (s.admissibleSampleVertex selector i).val ≠ (s.quad j.val).a :=
  fun h => (s.admissibleSampleVertex selector i).property
    (h ▸ sampledSwitching_root_mem s.graph T s.samples (s.boundary j.val))

omit [Fintype V] [Fintype ι] in
theorem full_second_inner_ne (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i j : s.AdmissibleSampleIndex selector) :
    (s.admissibleSecondVertex selector i).val ≠ (s.quad j.val).a :=
  fun h => (s.admissibleSecondVertex selector i).property
    (h ▸ sampledSwitching_root_mem s.graph T s.samples (s.boundary j.val))

omit [Fintype V] [Fintype ι] in
theorem full_first_outer_ne (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i j : s.AdmissibleSampleIndex selector) :
    (s.admissibleSampleVertex selector i).val ≠ (s.quad j.val).b := by
  intro he
  exact s.admissibleFirst_not_fullCore selector i
    (Or.inr ⟨s.admissibleBoundaryVertex selector j, ⟨s.boundary j.val,rfl⟩, he.symm⟩)

omit [Fintype V] [Fintype ι] in
theorem full_second_outer_ne (s : LabelledResamplingState V T ι) (selector : ℕ)
    (hs : 1 ≤ selector) (i j : s.AdmissibleSampleIndex selector) :
    (s.admissibleSecondVertex selector i).val ≠ (s.quad j.val).b := by
  intro he
  exact s.admissibleSecond_not_fullCore selector hs i
    (Or.inr ⟨s.admissibleBoundaryVertex selector j, ⟨s.boundary j.val,rfl⟩, he.symm⟩)

omit [Fintype V] [Fintype ι] in
theorem full_first_first_eq (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i j : s.AdmissibleSampleIndex selector) :
    (s.admissibleSampleVertex selector i).val = (s.admissibleSampleVertex selector j).val ↔ i = j :=
  Subtype.val_injective.eq_iff.trans (s.admissibleFirst_eq_iff selector i j)

omit [Fintype V] [Fintype ι] in
theorem full_second_second_eq (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i j : s.AdmissibleSampleIndex selector) :
    (s.admissibleSecondVertex selector i).val = (s.admissibleSecondVertex selector j).val ↔ i = j :=
  Subtype.val_injective.eq_iff.trans (s.admissibleSecond_eq_iff selector i j)

omit [Fintype V] [Fintype ι] in
theorem full_first_second_ne (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i j : s.AdmissibleSampleIndex selector) :
    (s.admissibleSampleVertex selector i).val ≠ (s.admissibleSecondVertex selector j).val :=
  fun h => s.admissibleFirst_eq_second_false selector i j (Subtype.ext h)

end LabelledResamplingState
end LocalLaw
