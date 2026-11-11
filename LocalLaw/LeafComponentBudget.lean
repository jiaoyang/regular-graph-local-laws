import LocalLaw.MultiLeafAugmentation
import LocalLaw.ComponentRestrictionBudget

/-! # Zero-deficit pendant leaves preserve the actual finite reference class

Every augmented component is explicitly isomorphic to the corresponding
core component with its own attached leaves. Deficit mass and Euler excess
are unchanged, including the positive-deficit alternative.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
namespace LocalLaw
local instance leafComponentBudgetDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V L:Type} [Fintype V] [Fintype L] {d:ℕ}

theorem component_finite_budget_of_pendant_leaves (g:DeficientGraph V d)(mate:L→V)
    (f:V⊕L→ℕ)(hdegree:∀a,(multiLeafGraph g.graph mate).degree a+f a≤d)
    (hcore:∀v,f (.inl v)=g.deficit v)(hleaf:∀l,f (.inr l)=0)
    (hbudget:g.ComponentFiniteReferenceBudget) :
    ({graph:=multiLeafGraph g.graph mate,deficit:=f,degree_deficit_le:=hdegree}:
      DeficientGraph (V⊕L) d).ComponentFiniteReferenceBudget := by
  let H:DeficientGraph (V⊕L) d:=⟨multiLeafGraph g.graph mate,f,hdegree⟩
  intro C
  let D:=(multiLeafComponentEquiv g.graph mate) C
  let e:=multiLeafComponentGraphIso g.graph mate C
  have heold (v:D.supp) : (e (.inl v)).val=.inl v.val:=rfl
  have heleaf (l:{l:L //mate l∈D.supp}) : (e (.inr l)).val=.inr l.val:=rfl
  have hsum : (∑v:C.supp,f v.val)=∑v:D.supp,g.deficit v.val := by
    have hh:=(Fintype.sum_equiv e.toEquiv
      (fun a=>f (e a).val) (fun v:C.supp=>f v.val) (fun _=>rfl))
    rw [←hh,Fintype.sum_sum_type]
    simp only [heold,heleaf,hcore,hleaf,Finset.sum_const_zero,add_zero]
    simp only [←finsum_eq_sum_of_fintype]
    rfl
  have hex : graphExcess (H.graph.induce C.supp)=graphExcess (g.graph.induce D.supp) := by
    have he:=graphExcess_iso e
    have hl:=multiLeafGraph_excess (g.graph.induce D.supp) (multiLeafComponentMate g.graph mate C)
    simp only [graphExcess,SimpleGraph.edgeFinset_card,←Nat.card_eq_fintype_card] at he hl ⊢
    exact he.symm.trans hl
  have hb:=hbudget D
  simp only [←finsum_eq_sum_of_fintype] at hsum
  rcases hb with hb | ⟨hb,v,hv⟩
  · left
    simp only [restrict,←finsum_eq_sum_of_fintype,graphExcess,SimpleGraph.edgeFinset_card,
      ←Nat.card_eq_fintype_card] at hb hex ⊢
    rw [hsum,hex]
    exact hb
  · right
    refine ⟨?_,e (.inl v),?_⟩
    · simp only [restrict,←finsum_eq_sum_of_fintype,graphExcess,SimpleGraph.edgeFinset_card,
        ←Nat.card_eq_fintype_card] at hb hex ⊢
      rw [hsum,hex]
      exact hb
    · change 0<f (.inl v.val)
      rw [hcore]
      exact hv

end DeficientGraph
end LocalLaw
