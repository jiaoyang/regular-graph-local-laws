import LocalLaw.ResamplingBoundaryLabels
import LocalLaw.DeficientGraphModel

/-!
# Actual outside deficit as a boundary-label fiber

The literal removed-neighbor count is identified with the fiber of any
boundary labeling. Finite indicator sums then give the exact conservation
law for every old/new labelled boundary swap.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance boundaryDeficitFibersDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A finite fiber count changes by the exact removed and inserted counts. -/
theorem conditional_fiber_count_conservation {I V : Type*} [Fintype I]
    (old new : I → V) (p : I → Prop) (v : V) :
    Nat.card {i : I // (if p i then new i else old i) = v} +
        Nat.card {i : I // p i ∧ old i = v} =
      Nat.card {i : I // old i = v} + Nat.card {i : I // p i ∧ new i = v} := by
  have hcard (q : I → Prop) : Nat.card {i : I // q i} = ∑ i : I, if q i then 1 else 0 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one]
  simp_rw [hcard, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : p i <;> simp only [hi, if_true, if_false, true_and, false_and]
  · exact Nat.add_comm _ _

namespace LabelledResamplingState
variable {V : Type*} {T : Set V} {ι : Type*}

def boundaryNeighborLabelEquiv (s : LabelledResamplingState V T ι) (v : (Tᶜ : Set V)) :
    {t : T // s.graph.Adj t.val v.val} ≃ {i : ι // (s.boundary i).val.2 = v.val} where
  toFun t :=
    let a : BoundaryOrientedEdge s.graph T := ⟨(t.val.val, v.val), t.property, t.val.property, v.property⟩
    ⟨s.boundary.symm a, by simp only [Equiv.apply_symm_apply]; rfl⟩
  invFun i := ⟨⟨(s.boundary i.val).val.1, (s.boundary i.val).property.2.1⟩, by
    have h := (s.boundary i.val).property.1
    simpa only [i.property] using h⟩
  left_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]
  right_inv i := by
    apply Subtype.ext
    apply s.boundary.injective
    dsimp only
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact i.property.symm

variable [Fintype ι]

theorem fullResample_boundary_fiber_conservation (s : LabelledResamplingState V T ι)
    (selector : ℕ) (v : (Tᶜ : Set V)) :
    Nat.card {i : ι // ((s.fullResample selector).boundary i).val.2 = v.val} +
        Nat.card {i : ι // s.Eligible selector i ∧ (s.boundary i).val.2 = v.val} =
      Nat.card {i : ι // (s.boundary i).val.2 = v.val} +
        Nat.card {i : ι // s.Eligible selector i ∧ (s.samples (s.boundary i)).val.2 = v.val} := by
  simp_rw [s.fullResample_boundary_outer]
  exact conditional_fiber_count_conservation _ _ _ _

end LabelledResamplingState
end LocalLaw
