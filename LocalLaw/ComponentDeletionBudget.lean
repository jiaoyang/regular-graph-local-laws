import LocalLaw.ComponentFiniteLocalization
import LocalLaw.RestrictionDeletionIdentity

/-!
# Deleting a connected set from componentwise reference models

Only the original component that meets the connected removed set acquires
deficit. Its actual cut components satisfy the positive-deficit extra class.
Untouched components stay in the base class. Component correspondence and
the source lost-degree convention are transported through actual graph maps.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance componentDeleteBudgetDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) canonicalComponentDeleteBudgetMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

omit [DecidableEq V] in
theorem componentwise_connected_deletion_budget (g : DeficientGraph V d)
    (hzero : ∀ v, g.deficit v = 0) (hbudget : g.ComponentReferenceBudget)
    (T : Set V) (hT : (g.graph.induce T).Connected) :
    (g.delete T).ComponentFiniteReferenceBudget := by
  intro c
  let H := outsideGraph g.graph T
  let gc := (g.delete T).restrict c.supp
  let a : c.supp := Classical.choice c.connected_induce_supp.nonempty
  let C := g.graph.connectedComponentMk a.val.val
  let gC := g.restrict C.supp
  have hCconn : gC.graph.Connected := C.connected_induce_supp
  have hCzero : ∀ v, gC.deficit v = 0 := fun v => hzero v.val
  have hCbudget : graphExcess gC.graph ≤ finiteOmega d := by
    have hh := hbudget C
    change (∑ v, gC.deficit v) + graphExcess gC.graph ≤ finiteOmega d at hh
    simpa only [hCzero, Finset.sum_const_zero, zero_add] using hh
  let incl : gc.graph →g g.graph :=
    { toFun := fun x => x.val.val
      map_rel' := fun h => h }
  have hcs : ∀ x : c.supp, x.val.val ∈ C.supp := by
    intro x
    obtain ⟨p⟩ := c.connected_induce_supp.preconnected a x
    exact (SimpleGraph.ConnectedComponent.sound (p.map incl).reachable).symm
  by_cases hmeet : ∃ t ∈ T, t ∈ C.supp
  · obtain ⟨t, ht, htC⟩ := hmeet
    have hTS : T ⊆ C.supp := by
      intro x hx
      obtain ⟨p⟩ := hT.preconnected ⟨t, ht⟩ ⟨x, hx⟩
      have hh := SimpleGraph.ConnectedComponent.sound (p.map (SimpleGraph.Embedding.induce T).toHom).reachable
      exact hh.symm.trans htC
    let TC : Set C.supp := {v | v.val ∈ T}
    let isoT : (gC.graph.induce TC) ≃g g.graph.induce T :=
      { toEquiv :=
          { toFun := fun v => ⟨v.val.val, v.property⟩
            invFun := fun v => ⟨⟨v.val, hTS v.property⟩, v.property⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        map_rel_iff' := Iff.rfl }
    have hTC : (gC.graph.induce TC).Connected := isoT.connected_iff.mpr hT
    let K := outsideGraph gC.graph TC
    let f : K →g H :=
      { toFun := fun v => ⟨v.val.val, v.property⟩
        map_rel' := fun h => h }
    let j : gc.graph →g K :=
      { toFun := fun x => ⟨⟨x.val.val, hcs x⟩, x.val.property⟩
        map_rel' := fun h => h }
    let D := K.connectedComponentMk (j a)
    have hDmem : ∀ x : c.supp, j x ∈ D.supp := by
      intro x
      obtain ⟨p⟩ := c.connected_induce_supp.preconnected a x
      exact (SimpleGraph.ConnectedComponent.sound (p.map j).reachable).symm
    have hcmem : ∀ x : D.supp, f x.val ∈ c.supp := by
      intro x
      obtain ⟨p⟩ := D.connected_induce_supp.preconnected ⟨j a, rfl⟩ x
      let ii : (K.induce D.supp) →g H :=
        { toFun := fun y => f y.val
          map_rel' := fun h => f.map_rel h }
      have hh := SimpleGraph.ConnectedComponent.sound (p.map ii).reachable
      exact hh.symm.trans a.property
    let e : gc.graph ≃g ((gC.delete TC).restrict D.supp).graph :=
      { toEquiv :=
          { toFun := fun x => ⟨j x, hDmem x⟩
            invFun := fun y => ⟨f y.val, hcmem y⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        map_rel_iff' := Iff.rfl }
    have hdef : ∀ x, gc.deficit x = ((gC.delete TC).restrict D.supp).deficit (e x) := by
      intro x
      exact (g.restrictionDeletion_deficit C.supp T TC (fun _ => Iff.rfl) hTS (j x)).symm
    have hsum : (∑ x, gc.deficit x) = ∑ y, ((gC.delete TC).restrict D.supp).deficit y :=
      Fintype.sum_equiv e.toEquiv _ _ hdef
    have hex := graphExcess_iso e
    have hh := gC.deleted_component_complexity hCzero TC hCconn hTC (finiteOmega d) hCbudget D
    apply Or.inr
    constructor
    · change (∑ x, gc.deficit x) + graphExcess gc.graph ≤ finiteOmega d + 1
      rw [hsum, hex]
      exact hh.2
    · obtain ⟨y, hy⟩ := hh.1
      refine ⟨e.symm y, ?_⟩
      change 0 < gc.deficit (e.symm y)
      rw [hdef, e.apply_symm_apply]
      exact hy
  · have hdelzero : ∀ x : c.supp, gc.deficit x = 0 := by
      intro x
      change (g.delete T).deficit x.val = 0
      rw [g.delete_deficit_eq_removed_neighbors, hzero]
      haveI : IsEmpty {t : T // g.graph.Adj t.val x.val.val} := ⟨fun t => by
        have htC : t.val.val ∈ C.supp := (C.mem_supp_congr_adj t.property).mpr (hcs x)
        exact hmeet ⟨t.val.val, t.val.property, htC⟩⟩
      simp only [Nat.card_of_isEmpty, zero_add]
    let f : gc.graph →g gC.graph :=
      { toFun := fun x => ⟨x.val.val, hcs x⟩
        map_rel' := fun h => h }
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun u : C.supp => u.val) h
    have hex := connected_embedding_graphExcess_le gc.graph gC.graph c.connected_induce_supp hCconn f hf
    apply Or.inl
    change (∑ x, gc.deficit x) + graphExcess gc.graph ≤ finiteOmega d
    simpa only [hdelzero, Finset.sum_const_zero, zero_add] using hex.trans hCbudget

end DeficientGraph
end LocalLaw
