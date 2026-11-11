import LocalLaw.DeletedLeafAugmentation
import LocalLaw.LeafComponentBudget

/-! # The lost-neighbor leaf model has the original finite reference class

Deleting physical vertices and splitting their incident edges into separate
zero-deficit leaves preserves the inherited restricted deficits. Pendant
augmentation then transfers the actual component class, with no increase of
the allowed threshold and no post-deletion reference-class hypothesis.
-/

noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance deletedLeafBudgetDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V:Type} [Fintype V] {d:ℕ}

theorem deletedLeafModel_component_finite_budget (g:DeficientGraph V d)(hd:1≤d)
    (T:Set V)(hbudget:g.ComponentFiniteReferenceBudget) :
    (g.deletedLeafModel hd T).ComponentFiniteReferenceBudget := by
  let core:DeficientGraph (Tᶜ:Set V) d:=
    {graph:=g.graph.induce Tᶜ,deficit:=fun v=>g.deficit v.val,degree_deficit_le:=by
      intro v
      have hh:=g.degree_deficit_le v.val
      have hdg:=induced_degree_le g.graph Tᶜ v
      simp only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] at hh hdg ⊢
      omega}
  let H:=g.deletedLeafModel hd T
  let mate:=deletedLeafMate g.graph T
  have hdegree : ∀a,(multiLeafGraph core.graph mate).degree a+H.deficit a≤d := by
    intro a
    exact H.degree_deficit_le a
  have hcoreBudget:core.ComponentFiniteReferenceBudget:=by
    have hb:=g.restrict_componentFiniteReferenceBudget Tᶜ hbudget
    intro C
    have hh:=hb C
    simp only [FiniteReferenceBudget,restrict,graphExcess,SimpleGraph.edgeFinset_card,
      ←Nat.card_eq_fintype_card,←finsum_eq_sum_of_fintype] at hh ⊢
    exact hh
  have hh:=core.component_finite_budget_of_pendant_leaves mate H.deficit hdegree
    (fun v=>g.deletedLeafModel_deficit_old hd T v)
    (fun l=>g.deletedLeafModel_deficit_leaf hd T l)
    hcoreBudget
  intro C
  have hC:=hh C
  simp only [FiniteReferenceBudget,restrict,graphExcess,SimpleGraph.edgeFinset_card,
    ←Nat.card_eq_fintype_card,←finsum_eq_sum_of_fintype] at hC ⊢
  exact hC

end DeficientGraph
end LocalLaw
