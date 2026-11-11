import LocalLaw.DeletedRestrictionBudget

/-! # Arbitrary restriction preserves the componentwise finite class

Each actual component of the restricted graph is a connected restriction
of the original graph, after flattening the two literal vertex subtypes.
The inherited deficits are unchanged by that isomorphism.
-/

noncomputable section
namespace LocalLaw

local instance componentRestrictionBudgetDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) canonicalComponentRestrictionBudgetMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

omit [DecidableEq V] in
theorem restrict_componentFiniteReferenceBudget (g : DeficientGraph V d) (K : Set V)
    (hbudget : g.ComponentFiniteReferenceBudget) : (g.restrict K).ComponentFiniteReferenceBudget := by
  intro c
  let f : c.supp → V := fun v => v.val.val
  have hf : Function.Injective f := fun _ _ h => Subtype.ext (Subtype.ext h)
  let S := Set.range f
  letI : Fintype S := @Subtype.fintype V (fun v => v ∈ S)
    (fun _ => Classical.propDecidable _) inferInstance
  let e : ((g.restrict K).graph.induce c.supp) ≃g g.graph.induce S :=
    { toEquiv := Equiv.ofInjective f hf
      map_rel_iff' := Iff.rfl }
  have hS : (g.graph.induce S).Connected := e.connected_iff.mp c.connected_induce_supp
  have hfinite := g.connected_restrict_finiteReferenceBudget S hS hbudget
  exact (g.restrict S).finiteReferenceBudget_of_iso ((g.restrict K).restrict c.supp) e
    (fun _ => rfl) hfinite

omit [DecidableEq V] in
theorem deleted_restriction_componentFiniteReferenceBudget
    (g : DeficientGraph V d) (M T : Set V) (hzero : ∀ v, g.deficit v = 0)
    (hM : (g.graph.induce M).Connected) (hT : (g.graph.induce T).Connected)
    (hTM : T ⊆ M) (hbudget : graphExcess (g.graph.induce M) ≤ finiteOmega d)
    (K : Set (Tᶜ : Set V)) (hKM : ∀ v ∈ K, v.val ∈ M) :
    ((g.delete T).restrict K).ComponentFiniteReferenceBudget := by
  intro c
  let f : c.supp → (Tᶜ : Set V) := fun v => v.val.val
  have hf : Function.Injective f := fun _ _ h => Subtype.ext (Subtype.ext h)
  let S := Set.range f
  letI : Fintype S := @Subtype.fintype (Tᶜ : Set V) (fun v => v ∈ S)
    (fun _ => Classical.propDecidable _) inferInstance
  let e : (((g.delete T).restrict K).graph.induce c.supp) ≃g (g.delete T).graph.induce S :=
    { toEquiv := Equiv.ofInjective f hf
      map_rel_iff' := Iff.rfl }
  have hS : ((g.delete T).graph.induce S).Connected := e.connected_iff.mp c.connected_induce_supp
  have hSM : ∀ v ∈ S, v.val ∈ M := by
    rintro _ ⟨v, rfl⟩
    exact hKM v.val.val v.val.property
  have hfinite := g.deleted_connected_restriction_finiteReferenceBudget M T hzero hM hT hTM hbudget S hS hSM
  exact ((g.delete T).restrict S).finiteReferenceBudget_of_iso
    (((g.delete T).restrict K).restrict c.supp) e (fun _ => rfl) hfinite

end DeficientGraph
end LocalLaw
