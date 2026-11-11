import LocalLaw.ComponentDeletionBudget
import LocalLaw.DeficientBudgetIso

/-! # A connected restriction of componentwise finite models is finite

The actual connected restricted graph lies in one genuine ambient component.
Restricting that component preserves its finite reference class, and the
literal subtype isomorphism transports both edges and inherited deficits.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw

local instance connectedRestrictionBudgetDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) canonicalConnectedRestrictionBudgetMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

omit [DecidableEq V] in
theorem connected_restrict_finiteReferenceBudget (g : DeficientGraph V d) (S : Set V)
    (hS : (g.graph.induce S).Connected) (hbudget : g.ComponentFiniteReferenceBudget) :
    (g.restrict S).FiniteReferenceBudget := by
  obtain ⟨a⟩ := hS.nonempty
  let c := g.graph.connectedComponentMk a.val
  have hSC : S ⊆ c.supp := by
    intro v hv
    obtain ⟨p⟩ := hS.preconnected a ⟨v, hv⟩
    exact (SimpleGraph.ConnectedComponent.sound
      (p.map (SimpleGraph.Embedding.induce S).toHom).reachable).symm
  let Sc : Set c.supp := {v | v.val ∈ S}
  let gc := g.restrict c.supp
  let e : (gc.graph.induce Sc) ≃g g.graph.induce S :=
    { toEquiv :=
        { toFun := fun v => ⟨v.val.val, v.property⟩
          invFun := fun v => ⟨⟨v.val, hSC v.property⟩, v.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      map_rel_iff' := Iff.rfl }
  have hSc : (gc.graph.induce Sc).Connected := e.connected_iff.mpr hS
  have hfinite := gc.restrict_finiteReferenceBudget Sc c.connected_induce_supp hSc (hbudget c)
  exact (gc.restrict Sc).finiteReferenceBudget_of_iso (g.restrict S) e.symm (fun _ => rfl) hfinite

end DeficientGraph
end LocalLaw
