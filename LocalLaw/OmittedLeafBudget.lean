import LocalLaw.OmittedLeafModels

/-! # The actual all-slot completion has the old finite reference class

Consuming every old lost-edge slot leaves the original inherited deficit.
The extra A slots consume its actual single boundary unit. The resulting
core is an old restriction with lowered deficits, and pendant augmentation
therefore proves the completed model's componentwise reference budget.
-/

noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance omittedLeafBudgetDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

def omittedOldCount (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))
    (v:(g.admissibleState T labels samples).OmittedCore selector S) : ℕ :=
  Nat.card {b:(g.admissibleState T labels samples).selectedFirstSet selector //
    (outsideGraph g.graph T).Adj b.val v.val.val}

def omittedOldRestoredModel (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N))) :=
  (g.omittedCommonModel T labels samples selector S).lowerDeficit
    (g.omittedOldCount T labels samples selector S) (by
      intro v
      rw [g.omittedCommonModel_deficit]
      exact Nat.le_add_left _ _)

omit [Fintype ι] in
theorem omittedOldRestoredModel_deficit (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))
    (v:(g.admissibleState T labels samples).OmittedCore selector S) :
    (g.omittedOldRestoredModel T labels samples selector S).deficit v=
      (g.deficient.delete T).deficit v.val.val := by
  change (g.omittedCommonModel T labels samples selector S).deficit v-
    g.omittedOldCount T labels samples selector S v=_
  rw [g.omittedCommonModel_deficit]
  exact Nat.add_sub_cancel _ _

omit [Fintype ι] in
theorem omittedOldRestoredModel_component_budget (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))
    (hb:((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget) :
    (g.omittedOldRestoredModel T labels samples selector S).ComponentFiniteReferenceBudget := by
  let s:=g.admissibleState T labels samples
  let K:Set S:={v |v.val∉s.selectedFirstSet selector}
  letI:DecidablePred (fun v:S=>v∈K):=fun _=>Classical.propDecidable _
  let old:=((g.deficient.delete T).restrict S).restrict K
  let C:=g.omittedOldRestoredModel T labels samples selector S
  let e:C.graph≃g old.graph:=
    {toEquiv:=
      {toFun:=fun v=>⟨⟨v.val.val,v.property⟩,v.val.property⟩
       invFun:=fun v=>⟨⟨v.val.val,v.property⟩,v.val.property⟩
       left_inv:=fun _=>rfl
       right_inv:=fun _=>rfl}
     map_rel_iff':=Iff.rfl}
  have hδ:∀v,C.deficit v=old.deficit (e v):=fun v=>g.omittedOldRestoredModel_deficit T labels samples selector S v
  exact old.componentFiniteReferenceBudget_of_iso C e hδ
    (((g.deficient.delete T).restrict S).restrict_componentFiniteReferenceBudget K hb)

def omittedAllCompletion (g:RegularGraph N d)(hd:1≤d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N))) :=
  (g.omittedCommonModel T labels samples selector S).attachLeaves hd
    ((g.admissibleState T labels samples).omittedAllMate selector S)
    (g.omittedAllMate_restore_budget T labels samples selector S)

theorem omittedAllCompletion_component_budget (g:RegularGraph N d)(hd:1≤d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))
    (hb:((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget) :
    (g.omittedAllCompletion hd T labels samples selector S).ComponentFiniteReferenceBudget := by
  let s:=g.admissibleState T labels samples
  let C:=g.omittedCommonModel T labels samples selector S
  let old:=g.omittedOldRestoredModel T labels samples selector S
  let ρ:=multiLeafMultiplicity (s.omittedExtraRoot selector S)
  have hρ:∀v,ρ v≤old.deficit v:=by
    intro v
    rw [g.omittedOldRestoredModel_deficit]
    exact g.omittedExtraMultiplicity_budget T labels samples selector S v
  let core:=old.lowerDeficit ρ hρ
  let H:=g.omittedAllCompletion hd T labels samples selector S
  have hc:core.ComponentFiniteReferenceBudget:=old.lowerDeficit_componentFiniteReferenceBudget ρ hρ
    (g.omittedOldRestoredModel_component_budget T labels samples selector S hb)
  have hcore:∀v,H.deficit (.inl v)=core.deficit v:=by
    intro v
    change C.deficit v-multiLeafMultiplicity (s.omittedAllMate selector S) v=
      (C.deficit v-g.omittedOldCount T labels samples selector S v)-ρ v
    rw [s.omittedAllMultiplicity]
    change C.deficit v-(g.omittedOldCount T labels samples selector S v+ρ v)=_
    exact Nat.sub_add_eq _ _ _
  have hh:=core.component_finite_budget_of_pendant_leaves (s.omittedAllMate selector S) H.deficit
    H.degree_deficit_le hcore (fun _=>rfl) hc
  intro c
  exact hh c

end RegularGraph
end LocalLaw
