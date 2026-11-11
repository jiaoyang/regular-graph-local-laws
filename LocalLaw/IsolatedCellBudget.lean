import LocalLaw.ComponentRestrictionBudget

/-! # Componentwise reference budgets for an actual isolated cell cover

A connected component cannot cross between cells with no cross edges.
Its actual inherited-deficit restriction is therefore a connected restriction
of one allowed cell model. This constructs the global component budget.
-/

noncomputable section
namespace LocalLaw

local instance isolatedCellBudgetDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) canonicalIsolatedCellBudgetMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

omit [DecidableEq V] in
theorem componentFiniteBudget_of_isolated_cover (g : DeficientGraph V d) (K : Set V)
    {I : Type*} (cell : I → Set V)
    (hcover : ∀ v ∈ K, ∃ i, v ∈ cell i)
    (hcross : ∀ i j, i ≠ j → ∀ v ∈ cell i, ∀ w ∈ cell j, ¬g.graph.Adj v w)
    (hbudget : ∀ i, (g.restrict (cell i)).ComponentFiniteReferenceBudget) :
    (g.restrict K).ComponentFiniteReferenceBudget := by
  intro c
  let a : c.supp := Classical.choice c.connected_induce_supp.nonempty
  obtain ⟨i, hi⟩ := hcover a.val.val a.val.property
  have hcomponent : ∀ x : c.supp, x.val.val ∈ cell i := by
    intro x
    obtain ⟨p⟩ := c.connected_induce_supp.preconnected a x
    let f : ((g.restrict K).graph.induce c.supp) →g g.graph.induce K :=
      { toFun := fun v => v.val, map_rel' := fun h => h }
    apply walk_end_mem_isolated (g.graph.induce K) {v : K | v.val ∈ cell i} ?_ (p.map f) hi
    intro v hv w hw hvw
    obtain ⟨j, hj⟩ := hcover w.val w.property
    have hji : i ≠ j := by intro heq; subst j; exact hw hj
    exact hcross i j hji v.val hv w.val hj hvw
  let f : c.supp → cell i := fun x => ⟨x.val.val, hcomponent x⟩
  have hf : Function.Injective f := by
    intro x y h
    have hraw : x.val.val = y.val.val := congrArg (fun v : cell i => v.val) h
    exact Subtype.ext (Subtype.ext hraw)
  let S := Set.range f
  letI : Fintype S := @Subtype.fintype (cell i) (fun v => v ∈ S)
    (fun _ => Classical.propDecidable _) inferInstance
  let e : ((g.restrict K).graph.induce c.supp) ≃g (g.restrict (cell i)).graph.induce S :=
    { toEquiv := Equiv.ofInjective f hf
      map_rel_iff' := Iff.rfl }
  have hS : ((g.restrict (cell i)).graph.induce S).Connected := e.connected_iff.mp c.connected_induce_supp
  have hfinite := (g.restrict (cell i)).connected_restrict_finiteReferenceBudget S hS (hbudget i)
  exact ((g.restrict (cell i)).restrict S).finiteReferenceBudget_of_iso ((g.restrict K).restrict c.supp) e
    (fun _ => rfl) hfinite

end DeficientGraph
end LocalLaw
