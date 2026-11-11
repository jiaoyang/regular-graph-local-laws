import LocalLaw.ConnectedRestrictionBudget

/-! # Actual finite class after deleting inside a common finite neighborhood

The common original model has zero inherited deficit and bounded excess.
Deleting the retained connected set gives the proved componentwise extended
class. Restricting to a connected deleted neighborhood and identifying its
literal lost-neighbor deficit then gives its finite reference budget.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw

local instance deletedRestrictionBudgetDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) canonicalDeletedRestrictionBudgetMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

omit [DecidableEq V] in
theorem deleted_connected_restriction_finiteReferenceBudget
    (g : DeficientGraph V d) (M T : Set V) (hzero : ∀ v, g.deficit v = 0)
    (hM : (g.graph.induce M).Connected) (hT : (g.graph.induce T).Connected)
    (hTM : T ⊆ M) (hbudget : graphExcess (g.graph.induce M) ≤ finiteOmega d)
    (K : Set (Tᶜ : Set V)) (hK : ((g.delete T).graph.induce K).Connected)
    (hKM : ∀ v ∈ K, v.val ∈ M) :
    ((g.delete T).restrict K).FiniteReferenceBudget := by
  let gM := g.restrict M
  let Tm : Set M := {v | v.val ∈ T}
  have hMzero : ∀ v, gM.deficit v = 0 := fun v => hzero v.val
  have hMbudget : gM.ComponentReferenceBudget := by
    intro c
    have hex := connected_induce_graphExcess_le gM.graph c.supp hM c.connected_induce_supp
    have hb : graphExcess gM.graph ≤ finiteOmega d := hbudget
    have hh := hex.trans hb
    change (∑ v : c.supp, gM.deficit v.val) + graphExcess (gM.graph.induce c.supp) ≤ finiteOmega d
    simpa only [hMzero, Finset.sum_const_zero, zero_add] using hh
  let isoT : (gM.graph.induce Tm) ≃g g.graph.induce T :=
    { toEquiv :=
        { toFun := fun v => ⟨v.val.val, v.property⟩
          invFun := fun v => ⟨⟨v.val, hTM v.property⟩, v.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      map_rel_iff' := Iff.rfl }
  have hTm : (gM.graph.induce Tm).Connected := isoT.connected_iff.mpr hT
  let D := gM.delete Tm
  have hD : D.ComponentFiniteReferenceBudget :=
    gM.componentwise_connected_deletion_budget hMzero hMbudget Tm hTm
  let U : Set (Tmᶜ : Set M) := {v | (⟨v.val.val, v.property⟩ : (Tᶜ : Set V)) ∈ K}
  let e : (D.graph.induce U) ≃g (g.delete T).graph.induce K :=
    { toEquiv :=
        { toFun := fun v => ⟨⟨v.val.val.val, v.val.property⟩, v.property⟩
          invFun := fun v => ⟨⟨⟨v.val.val, hKM v.val v.property⟩, v.val.property⟩, v.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      map_rel_iff' := Iff.rfl }
  have hU : (D.graph.induce U).Connected := e.connected_iff.mpr hK
  have hUbudget := D.connected_restrict_finiteReferenceBudget U hU hD
  apply (D.restrict U).finiteReferenceBudget_of_iso ((g.delete T).restrict K) e.symm ?_ hUbudget
  intro v
  exact (g.restrictionDeletion_deficit M T Tm (fun _ => Iff.rfl) hTM (e.symm v).val).symm

end DeficientGraph
end LocalLaw
