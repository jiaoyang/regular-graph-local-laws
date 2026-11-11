import LocalLaw.DeficitBudgetMonotoneIso
import LocalLaw.PartialDeletionBoundaryDefect
import LocalLaw.ComponentDeletionBudget
import LocalLaw.ComponentRestrictionBudget

/-! Deleting a retained part of one connected removed set.
The retained part can be disconnected. Omitted removed neighbors decrease the
inherited deficits, preserving the finite class after exact graph transport. -/
noncomputable section
namespace LocalLaw
local instance partialRestrictionDeletionBudgetDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V:Type}[Fintype V]{d:ℕ}

theorem partial_restrictionDeletion_component_budget (g:DeficientGraph V d)
    (hzero:∀v,g.deficit v=0)(hb:g.ComponentReferenceBudget)
    (T:Set V)(hT:(g.graph.induce T).Connected)
    (S:Set V)(Tm:Set S)(hTm:∀v:S,v∈Tm↔v.val∈T):
    ((g.restrict S).delete Tm).ComponentFiniteReferenceBudget:=by
  letI:DecidableEq V:=Classical.decEq _
  let K:Set (Tᶜ:Set V):={v|v.val∈S}
  let M:=(g.delete T).restrict K
  let H:=(g.restrict S).delete Tm
  let e:H.graph≃g M.graph:=restrictionDeletionGraphIso g.graph S T Tm hTm
  have hglobal:=(g.componentwise_connected_deletion_budget hzero hb T hT)
  have hm:= (g.delete T).restrict_componentFiniteReferenceBudget K hglobal
  exact M.componentFiniteReferenceBudget_mono_iso H e (fun v=>by
    have hh:=g.partial_restrictionDeletion_deficit S T Tm hTm v
    change M.deficit (e v)=H.deficit v+_ at hh
    omega) hm

end DeficientGraph
end LocalLaw
