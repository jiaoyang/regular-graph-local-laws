import LocalLaw.SelectedFirstNeighborCharge
import LocalLaw.DeletedLeafAugmentation

/-! # Actual weighted new-neighbor charge, with repeated old mates retained -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance selectedFirstWeightedChargeDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {I K : Type}[Fintype I][Fintype K]
theorem finite_fiber_weight_sum (e : I→K)(w : K→ℝ) :
    (∑v:K,(Nat.card {i:I // e i=v}:ℝ)*w v)=∑i:I,w (e i) := by
  classical
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card] using
    Fintype.sum_fiberwise' e w

namespace LabelledResamplingState
variable {V : Type}[Fintype V]{T : Set V}{ι : Type}[Fintype ι]

def admissibleBoundaryCommonVertex (s : LabelledResamplingState V T ι)(selector : ℕ)
    (i : s.AdmissibleSampleIndex selector) : ((s.selectedFirstSet selector)ᶜ : Set (Tᶜ : Set V)) :=
  ⟨s.admissibleBoundaryVertex selector i,s.admissibleBoundaryVertex_not_selectedFirst selector i⟩

theorem selectedFirst_weighted_neighbor_charge (s : LabelledResamplingState V T ι)(selector : ℕ)
    (w : ((s.selectedFirstSet selector)ᶜ : Set (Tᶜ : Set V))→ℝ)(hw : ∀v,0≤w v) :
    (∑v:((s.selectedFirstSet selector)ᶜ : Set (Tᶜ : Set V)),
      (Nat.card {b:s.selectedFirstSet selector //
        (outsideGraph (s.fullResample selector).graph T).Adj b.val v.val}:ℝ)*w v) ≤
      (∑l:DeletedLeafIndex (outsideGraph s.graph T) (s.selectedFirstSet selector),w l.1)+
        ∑i:s.AdmissibleSampleIndex selector,w (s.admissibleBoundaryCommonVertex selector i) := by
  have hc (v:((s.selectedFirstSet selector)ᶜ : Set (Tᶜ : Set V))) :
      (Nat.card {i:s.AdmissibleSampleIndex selector // v.val=s.admissibleBoundaryVertex selector i}:ℝ)=
        (Nat.card {i:s.AdmissibleSampleIndex selector // s.admissibleBoundaryCommonVertex selector i=v}:ℝ) := by
    congr 1
    apply Nat.card_congr
    exact {toFun := fun i => ⟨i.val,Subtype.ext i.property.symm⟩
           invFun := fun i => ⟨i.val,(congrArg Subtype.val i.property).symm⟩
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl}
  calc
    _ ≤ ∑v:((s.selectedFirstSet selector)ᶜ : Set (Tᶜ : Set V)),
      ((Nat.card {b:s.selectedFirstSet selector // (outsideGraph s.graph T).Adj b.val v.val}:ℝ)+
        (Nat.card {i:s.AdmissibleSampleIndex selector // v.val=s.admissibleBoundaryVertex selector i}:ℝ))*w v := by
      apply Finset.sum_le_sum
      intro v _
      apply mul_le_mul_of_nonneg_right _ (hw v)
      exact_mod_cast s.selectedFirst_new_neighbor_count_le selector v.val
    _ = (∑v:((s.selectedFirstSet selector)ᶜ : Set (Tᶜ : Set V)),
      (Nat.card {b:s.selectedFirstSet selector // (outsideGraph s.graph T).Adj b.val v.val}:ℝ)*w v)+
        ∑i:s.AdmissibleSampleIndex selector,w (s.admissibleBoundaryCommonVertex selector i) := by
      simp only [add_mul,Finset.sum_add_distrib,hc]
      rw [finite_fiber_weight_sum]
    _ = _ := by
      congr 1
      simp only [DeletedLeafIndex,Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,
        nsmul_eq_mul,Nat.card_eq_fintype_card]

end LabelledResamplingState
end LocalLaw
