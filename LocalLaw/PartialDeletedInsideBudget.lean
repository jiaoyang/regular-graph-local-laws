import LocalLaw.PartialRestrictionDeletionBudget
import LocalLaw.SourceFullRestrictionGeometry

/-! Partial deletion inside a larger old finite reference model.
No connectedness of the retained removed set is imposed. -/
noncomputable section
namespace LocalLaw
local instance partialDeletedInsideBudgetDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V:Type}[Fintype V]{d:ℕ}

theorem partial_deleted_inside_component_budget (g:DeficientGraph V d)
    (M T S:Set V)(hzero:∀v,g.deficit v=0)
    (hb:(g.restrict M).ComponentReferenceBudget)(hT:(g.graph.induce T).Connected)
    (hTM:T⊆M)(hSM:S⊆M)(Tm:Set S)(hTm:∀v:S,v∈Tm↔v.val∈T):
    ((g.restrict S).delete Tm).ComponentFiniteReferenceBudget:=by
  letI:DecidableEq V:=Classical.decEq _
  let TM:Set M:={v|v.val∈T}
  let K:Set (TMᶜ:Set M):={v|v.val.val∈S}
  let old:=(g.restrict M).delete TM
  let G:=old.restrict K
  let H:=(g.restrict S).delete Tm
  let isoT:=inducePreimageIso g.graph M T hTM
  have hTMconn:((g.restrict M).graph.induce TM).Connected:=isoT.connected_iff.mpr hT
  have ho:= (g.restrict M).componentwise_connected_deletion_budget (fun v=>hzero v.val) hb TM hTMconn
  have hG:=old.restrict_componentFiniteReferenceBudget K ho
  let e:H.graph≃g G.graph:=
    { toEquiv:=
        { toFun:=fun v=>⟨⟨⟨v.val.val,hSM v.val.property⟩,fun ht=>v.property ((hTm v.val).mpr ht)⟩,v.val.property⟩
          invFun:=fun v=>⟨⟨v.val.val.val,v.property⟩,fun ht=>v.val.property ((hTm ⟨v.val.val.val,v.property⟩).mp ht)⟩
          left_inv:=fun _=>rfl
          right_inv:=fun _=>rfl }
      map_rel_iff':=Iff.rfl }
  apply G.componentFiniteReferenceBudget_mono_iso H e ?_ hG
  intro v
  change ((g.restrict S).delete Tm).deficit v≤((g.restrict M).delete TM).deficit (e v).val
  rw [(g.restrict S).delete_deficit_eq_removed_neighbors,(g.restrict M).delete_deficit_eq_removed_neighbors]
  apply Nat.add_le_add_left
  let f:{t:Tm//(g.graph.induce S).Adj t.val v.val}→{t:TM//(g.graph.induce M).Adj t.val (e v).val.val}:=
    fun t=>⟨⟨⟨t.val.val.val,hSM t.val.val.property⟩,(hTm t.val.val).mp t.val.property⟩,t.property⟩
  apply Nat.card_le_card_of_injective f
  intro a b hab
  exact Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun t=>t.val.val.val) hab)))

end DeficientGraph
end LocalLaw
