import LocalLaw.OmittedOldCompletion
import LocalLaw.OmittedLeafDiameter

/-! # The correct all-old-slot completion inherits the old local class

Slots whose removed B lies outside the local set remain present. Restoring
all of them leaves exactly the inherited old deficit, without losing any
omitted-neighbor charge.
-/

noncomputable section
namespace LocalLaw
local instance omittedOldCompletionBudgetDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}{ι : Type}[Fintype ι]

omit [Fintype ι] in
theorem omittedOldCompletion_component_budget (g : RegularGraph N d)(hd : 1≤d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector : ℕ)(S : Set (Tᶜ:Set (Fin N)))
    (hb : ((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget) :
    (g.omittedOldCompletion hd T labels samples selector S).ComponentFiniteReferenceBudget := by
  let s := g.admissibleState T labels samples
  let core := g.omittedOldRestoredModel T labels samples selector S
  let H := g.omittedOldCompletion hd T labels samples selector S
  have hc := g.omittedOldRestoredModel_component_budget T labels samples selector S hb
  have hδ : ∀v,H.deficit (.inl v)=core.deficit v := by
    intro v
    rw [g.omittedOldCompletion_core_deficit,g.omittedOldRestoredModel_deficit]
  have hdeg : ∀v,(multiLeafGraph core.graph (Sigma.fst : s.OmittedOldLeaves selector S → s.OmittedCore selector S)).degree v+H.deficit v≤d := by
    intro v
    simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using H.degree_deficit_le v
  have hh := core.component_finite_budget_of_pendant_leaves
    (Sigma.fst : s.OmittedOldLeaves selector S → s.OmittedCore selector S) H.deficit
    hdeg hδ (fun _ => rfl) hc
  intro c
  simpa only [DeficientGraph.FiniteReferenceBudget,DeficientGraph.restrict,graphExcess,
    SimpleGraph.edgeFinset_card,←Nat.card_eq_fintype_card,←finsum_eq_sum_of_fintype] using hh c

omit [Fintype ι] in
theorem omittedOldCompletion_diameter (g : RegularGraph N d)(hd : 1≤d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector : ℕ)(S : Set (Tᶜ:Set (Fin N)))
    (hb : ((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget)
    (D : ℕ)(hD : ∀u v,((g.deficient.delete T).restrict S).graph.dist u v≤D)
    (u v : (g.admissibleState T labels samples).OmittedCore selector S ⊕
      (g.admissibleState T labels samples).OmittedOldLeaves selector S) :
    (g.omittedOldCompletion hd T labels samples selector S).graph.dist u v≤hereditaryReferenceRadius d D+2 := by
  exact multiLeafGraph_diameter_bound _ _ _
    (g.omittedCommonModel_diameter T labels samples selector S hb D hD) u v

end RegularGraph
end LocalLaw
