import LocalLaw.SelectedFirstCutCouplingRows
import LocalLaw.SelectedCommonCapture

/-! # Actual selected-B coupling inside the old augmented comparison region

Containing every selected B endpoint identifies its local removed mask with
the global selected set. Every accepted A root is also retained. The actual
new restricted cut row is therefore charged to literal old local slots.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2800000
namespace LocalLaw
local instance selectedFirstRegionChargeDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type}[Fintype V]{T : Set V}{ι : Type}[Fintype ι]

def selectedFirstRegionEquiv (s : LabelledResamplingState V T ι)(selector : ℕ)
    (A : Set (Tᶜ:Set V))(hA : s.selectedFirstSet selector⊆A) :
    s.partialFirstRemovedSet selector A ≃ s.selectedFirstSet selector where
  toFun b := ⟨b.val.val,b.property⟩
  invFun b := ⟨⟨b.val,hA b.property⟩,b.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def selectedFirstRegionNeighborEquiv (s : LabelledResamplingState V T ι)(selector : ℕ)
    (A : Set (Tᶜ:Set V))(hA : s.selectedFirstSet selector⊆A)(F : SimpleGraph (Tᶜ:Set V))(v : A) :
    {b:s.partialFirstRemovedSet selector A // (F.induce A).Adj b.val v} ≃
      {b:s.selectedFirstSet selector // F.Adj b.val v.val} where
  toFun b := ⟨s.selectedFirstRegionEquiv selector A hA b.val,b.property⟩
  invFun b := ⟨(s.selectedFirstRegionEquiv selector A hA).symm b.val,b.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def regionalBoundaryCommonVertex (s : LabelledResamplingState V T ι)(selector : ℕ)
    (A : Set (Tᶜ:Set V))(hAi : ∀i:s.AdmissibleSampleIndex selector,s.admissibleBoundaryVertex selector i∈A)
    (i : s.AdmissibleSampleIndex selector) : ((s.partialFirstRemovedSet selector A)ᶜ:Set A) :=
  ⟨⟨s.admissibleBoundaryVertex selector i,hAi i⟩,s.admissibleBoundaryVertex_not_selectedFirst selector i⟩

theorem selectedFirst_region_neighbor_count_le (s : LabelledResamplingState V T ι)(selector : ℕ)
    (A : Set (Tᶜ:Set V))(hA : s.selectedFirstSet selector⊆A)
    (hAi : ∀i:s.AdmissibleSampleIndex selector,s.admissibleBoundaryVertex selector i∈A)
    (v : ((s.partialFirstRemovedSet selector A)ᶜ:Set A)) :
    Nat.card {b:s.partialFirstRemovedSet selector A //
      ((outsideGraph (s.fullResample selector).graph T).induce A).Adj b.val v.val} ≤
    Nat.card {b:s.partialFirstRemovedSet selector A //
      ((outsideGraph s.graph T).induce A).Adj b.val v.val}+
      Nat.card {i:s.AdmissibleSampleIndex selector // s.regionalBoundaryCommonVertex selector A hAi i=v} := by
  have h := s.selectedFirst_new_neighbor_count_le selector v.val.val
  rw [←Nat.card_congr (s.selectedFirstRegionNeighborEquiv selector A hA _ v.val),
      ←Nat.card_congr (s.selectedFirstRegionNeighborEquiv selector A hA (outsideGraph s.graph T) v.val)] at h
  have he : {i:s.AdmissibleSampleIndex selector // v.val.val=s.admissibleBoundaryVertex selector i} ≃
      {i:s.AdmissibleSampleIndex selector // s.regionalBoundaryCommonVertex selector A hAi i=v} :=
    {toFun := fun i => ⟨i.val,Subtype.ext (Subtype.ext i.property.symm)⟩
     invFun := fun i => ⟨i.val,(congrArg (fun w:((s.partialFirstRemovedSet selector A)ᶜ:Set A) => w.val.val) i.property).symm⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl}
  simpa only [Nat.card_congr he] using h

theorem selectedFirst_region_weighted_charge (s : LabelledResamplingState V T ι)(selector : ℕ)
    (A : Set (Tᶜ:Set V))(hA : s.selectedFirstSet selector⊆A)
    (hAi : ∀i:s.AdmissibleSampleIndex selector,s.admissibleBoundaryVertex selector i∈A)
    (w : ((s.partialFirstRemovedSet selector A)ᶜ:Set A)→ℝ)(hw : ∀v,0≤w v) :
    (∑v:((s.partialFirstRemovedSet selector A)ᶜ:Set A),
      (Nat.card {b:s.partialFirstRemovedSet selector A //
        ((outsideGraph (s.fullResample selector).graph T).induce A).Adj b.val v.val}:ℝ)*w v) ≤
      (∑l:DeletedLeafIndex ((outsideGraph s.graph T).induce A) (s.partialFirstRemovedSet selector A),w l.1)+
        ∑i:s.AdmissibleSampleIndex selector,w (s.regionalBoundaryCommonVertex selector A hAi i) := by
  calc
    _ ≤ ∑v:((s.partialFirstRemovedSet selector A)ᶜ:Set A),
      ((Nat.card {b:s.partialFirstRemovedSet selector A // ((outsideGraph s.graph T).induce A).Adj b.val v.val}:ℝ)+
        (Nat.card {i:s.AdmissibleSampleIndex selector // s.regionalBoundaryCommonVertex selector A hAi i=v}:ℝ))*w v := by
      apply Finset.sum_le_sum
      intro v _
      apply mul_le_mul_of_nonneg_right _ (hw v)
      exact_mod_cast s.selectedFirst_region_neighbor_count_le selector A hA hAi v
    _ = _ := by
      simp only [add_mul,Finset.sum_add_distrib,finite_fiber_weight_sum]
      congr 1
      simp only [DeletedLeafIndex,Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,
        nsmul_eq_mul,Nat.card_eq_fintype_card]

theorem selectedFirst_region_new_cut_product_rows (s : LabelledResamplingState V T ι)
    (d selector : ℕ)(A : Set (Tᶜ:Set V))(hA : s.selectedFirstSet selector⊆A)
    (hAi : ∀i:s.AdmissibleSampleIndex selector,s.admissibleBoundaryVertex selector i∈A)
    (a : ((s.partialFirstRemovedSet selector A)ᶜ:Set A)→ℂ) :
    (∑b:s.partialFirstRemovedSet selector A,
      ‖∑v:((s.partialFirstRemovedSet selector A)ᶜ:Set A),a v*
        normalizedAdjacency ((outsideGraph (s.fullResample selector).graph T).induce A) d v.val b.val‖) ≤
      (Real.sqrt ((d:ℝ)-1))⁻¹ *
        ((∑l:DeletedLeafIndex ((outsideGraph s.graph T).induce A) (s.partialFirstRemovedSet selector A),‖a l.1‖)+
          ∑i:s.AdmissibleSampleIndex selector,‖a (s.regionalBoundaryCommonVertex selector A hAi i)‖) := by
  have hn := normalized_cut_product_row_sum ((outsideGraph (s.fullResample selector).graph T).induce A) d
    (s.partialFirstRemovedSet selector A)ᶜ (s.partialFirstRemovedSet selector A) a
  have hc := s.selectedFirst_region_weighted_charge selector A hA hAi (fun v => ‖a v‖) (fun v => norm_nonneg _)
  simp only [←finsum_eq_sum_of_fintype] at hn hc ⊢
  exact hn.trans (mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr (Real.sqrt_nonneg _)))

end LabelledResamplingState
end LocalLaw
