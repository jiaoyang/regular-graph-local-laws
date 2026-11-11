import LocalLaw.CoreBoundaryConvolution
import LocalLaw.CavityTreeFeedback

/-!
# Actual ordinary and exceptional deleted components for localization

The exceptional cut charge is an actual Euler invariant. Its total controls
the number of attachment edges, while charge-zero components are genuine
one-attachment cavity trees with their exact pointwise deletion deficit.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance localizationComponentsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem cut_charge_zero_iff (G : SimpleGraph V) (S : Set V)
    (hG : G.Connected) (hS : S.Nonempty) (c : CutComponent G S) :
    cutExcessCharge G S c = 0 ↔
      graphExcess (cutComponentGraph G S c) = 0 ∧ cutMultiplicity G S c = 1 := by
  have hh := cutExcessCharge_add_one G S hG hS c
  have hp := cutMultiplicity_positive G S hG hS c
  simp only [graphExcess, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hh ⊢
  omega

/-- All ordinary outside components are actual trees with one attachment. -/
theorem ordinary_cut_component_isTree (G : SimpleGraph V) (S : Set V)
    (hG : G.Connected) (hS : S.Nonempty) (c : CutComponent G S)
    (hcharge : cutExcessCharge G S c = 0) :
    (cutComponentGraph G S c).IsTree ∧ cutMultiplicity G S c = 1 := by
  have hh := (cut_charge_zero_iff G S hG hS c).mp hcharge
  refine ⟨connected_excess_zero_isTree _
    (SimpleGraph.ConnectedComponent.connected_induce_supp c) ?_, hh.2⟩
  have he := hh.1
  simp only [graphExcess, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at he ⊢
  exact he

private theorem numeric_exceptional_mass {I : Type*} [Fintype I]
    (charge mult : I → ℕ) (h : ∀ i, mult i ≤ charge i + 1) :
    (∑ i, if 0 < charge i then mult i else 0) ≤ 2 * ∑ i, charge i := by
  calc
    _ ≤ ∑ i, 2 * charge i := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · exact (h i).trans (by omega)
      · exact Nat.zero_le _
    _ = _ := (Finset.mul_sum ..).symm

private theorem numeric_positive_card {I : Type*} [Fintype I] (charge : I → ℕ) :
    Nat.card {i // 0 < charge i} ≤ ∑ i, charge i := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · exact hi
  · exact Nat.zero_le _

/-- The original Euler excess pays for every exceptional attachment,
including single-attachment components which contain a cycle. The enumeration-
free sum avoids choosing a particular finite listing of the components. -/
theorem exceptional_cut_attachment_sum (G : SimpleGraph V) (S : Set V)
    (hG : G.Connected) (hS : (G.induce S).Connected) (ω : ℕ) (hω : graphExcess G ≤ ω) :
    (∑ᶠ c : CutComponent G S,
      if 0 < cutExcessCharge G S c then cutMultiplicity G S c else 0) ≤ 2 * ω := by
  have hSne : S.Nonempty := by obtain ⟨v⟩ := hS.nonempty; exact ⟨v.val, v.property⟩
  have hEuler := connected_cutset_excess_identity G S hG hS
  have hsum : (∑ᶠ c : CutComponent G S, cutExcessCharge G S c) ≤ ω := by
    simp only [graphExcess, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
      ← finsum_eq_sum_of_fintype] at hEuler hω
    omega
  have hmult : ∀ c, cutMultiplicity G S c ≤ cutExcessCharge G S c + 1 := by
    intro c
    have hh := cutExcessCharge_add_one G S hG hSne c
    have hm := Nat.le_add_left (cutMultiplicity G S c) (graphExcess (cutComponentGraph G S c))
    simp only [graphExcess, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hh hm
    exact hm.trans_eq hh.symm
  have hnum := numeric_exceptional_mass (cutExcessCharge G S) (cutMultiplicity G S) hmult
  simp only [← finsum_eq_sum_of_fintype] at hnum
  exact hnum.trans (Nat.mul_le_mul_left 2 hsum)

theorem exceptional_cut_component_count (G : SimpleGraph V) (S : Set V)
    (hG : G.Connected) (hS : (G.induce S).Connected) (ω : ℕ) (hω : graphExcess G ≤ ω) :
    Nat.card {c : CutComponent G S // 0 < cutExcessCharge G S c} ≤ ω := by
  have hEuler := connected_cutset_excess_identity G S hG hS
  have hsum : (∑ᶠ c : CutComponent G S, cutExcessCharge G S c) ≤ ω := by
    simp only [graphExcess, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
      ← finsum_eq_sum_of_fintype] at hEuler hω
    omega
  have hnum := numeric_positive_card (cutExcessCharge G S)
  simp only [← finsum_eq_sum_of_fintype] at hnum
  exact hnum.trans hsum

/-- Every literal ordinary boundary edge identifies the genuine cavity
root and its exact one-unit deficit. -/
theorem ordinary_cut_root_deficit (G : SimpleGraph V) (S : Set V)
    (hG : G.Connected) (hS : S.Nonempty) (c : CutComponent G S)
    (hcharge : cutExcessCharge G S c = 0) (e : CutBoundaryEdge G S c) (v : c.supp) :
    cutDeficit G S c v = if v = cutAttachmentRoot G S c e then 1 else 0 :=
  cutDeficit_of_unique_boundary G S c ((cut_charge_zero_iff G S hG hS c).mp hcharge).2 e v

end LocalLaw
