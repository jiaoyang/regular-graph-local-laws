import LocalLaw.LeafComponentBudget
import LocalLaw.DeficitReduction

/-! # Consuming arbitrary deficit units by leaves preserves the reference class -/

noncomputable section
namespace LocalLaw
local instance attachedLeafBudgetDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V L:Type} [Fintype V] [Fintype L] [DecidableEq V] {d:ℕ}

theorem attachLeaves_componentFiniteReferenceBudget (g:DeficientGraph V d)(hd:1≤d)
    (mate:L→V)(hrestore:∀v,multiLeafMultiplicity mate v≤g.deficit v)
    (hb:g.ComponentFiniteReferenceBudget) :
    (g.attachLeaves hd mate hrestore).ComponentFiniteReferenceBudget := by
  let core:=g.lowerDeficit (multiLeafMultiplicity mate) hrestore
  let H:=g.attachLeaves hd mate hrestore
  have hc:core.ComponentFiniteReferenceBudget:=g.lowerDeficit_componentFiniteReferenceBudget _ _ hb
  have hh:=core.component_finite_budget_of_pendant_leaves mate H.deficit H.degree_deficit_le
    (fun _=>rfl) (fun _=>rfl) hc
  intro C
  exact hh C

end DeficientGraph
end LocalLaw
