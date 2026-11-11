import LocalLaw.PartialDeletedInsideBudget

/-! Global deletion inside a componentwise finite old model. -/
noncomputable section
namespace LocalLaw
local instance globalDeletedInsideBudgetDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V:Type}[Fintype V]{d:ℕ}

theorem global_deleted_inside_component_budget (g:DeficientGraph V d)(M T:Set V)
    (hzero:∀v,g.deficit v=0)(hb:(g.restrict M).ComponentReferenceBudget)
    (hT:(g.graph.induce T).Connected)(hTM:T⊆M)
    (K:Set (Tᶜ:Set V))(hKM:∀v∈K,v.val∈M):
    ((g.delete T).restrict K).ComponentFiniteReferenceBudget:=by
  let TM:Set M:={v|v.val∈T}
  let KM:Set (TMᶜ:Set M):={v|⟨v.val.val,v.property⟩∈K}
  let old:=(g.restrict M).delete TM
  let G:=old.restrict KM
  let H:=(g.delete T).restrict K
  let isoT:=inducePreimageIso g.graph M T hTM
  have hTMconn:((g.restrict M).graph.induce TM).Connected:=isoT.connected_iff.mpr hT
  have ho:=(g.restrict M).componentwise_connected_deletion_budget (fun v=>hzero v.val) hb TM hTMconn
  have hG:=old.restrict_componentFiniteReferenceBudget KM ho
  let e:H.graph≃g G.graph:=
    { toEquiv:=
        { toFun:=fun v=>⟨⟨⟨v.val.val,hKM v.val v.property⟩,v.val.property⟩,v.property⟩
          invFun:=fun v=>⟨⟨v.val.val.val,v.val.property⟩,v.property⟩
          left_inv:=fun _=>rfl
          right_inv:=fun _=>rfl }
      map_rel_iff':=Iff.rfl }
  apply G.componentFiniteReferenceBudget_of_iso H e ?_ hG
  intro v
  exact (g.restrictionDeletion_deficit M T TM (fun _=>Iff.rfl) hTM (e v).val).symm

end DeficientGraph
end LocalLaw
