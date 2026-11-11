import LocalLaw.DeficitReduction

/-! Finite reference budgets under graph isomorphism and deficit decrease. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance deficitBudgetMonotoneIsoDecidable (p:Prop):Decidable p:=Classical.propDecidable p
local instance (priority := high) deficitBudgetMonotoneComponentMem {A : Type} (G : SimpleGraph A)
    (c : G.ConnectedComponent) : DecidablePred (fun x=>x∈c.supp) := fun _=>Classical.propDecidable _
namespace DeficientGraph
variable {V W:Type}[Fintype V][Fintype W]{d:ℕ}

theorem finiteReferenceBudget_mono_iso (g:DeficientGraph V d)(h:DeficientGraph W d)
    (e:h.graph≃g g.graph)(hδ:∀v,h.deficit v≤g.deficit (e v))
    (hb:g.FiniteReferenceBudget):h.FiniteReferenceBudget:=by
  have hsum:(∑v,h.deficit v)≤∑v,g.deficit v:=by
    calc
      _≤∑v,g.deficit (e v):=Finset.sum_le_sum (fun v _=>hδ v)
      _=∑v,g.deficit v:=e.toEquiv.sum_comp _
  have hcomplex:(∑v,h.deficit v)+graphExcess h.graph≤(∑v,g.deficit v)+graphExcess g.graph:=by
    rw [graphExcess_iso e]
    exact Nat.add_le_add_right hsum _
  rcases hb with hb|⟨hb,v,hv⟩
  · exact Or.inl (hcomplex.trans hb)
  · by_cases hp:∃w,0<h.deficit w
    · exact Or.inr ⟨hcomplex.trans hb,hp⟩
    · have hz:∀w,h.deficit w=0:=by
        intro w
        by_contra hw
        exact hp ⟨w,Nat.pos_of_ne_zero hw⟩
      have hpos:1≤∑w,g.deficit w:=Nat.succ_le_of_lt
        (hv.trans_le (Finset.single_le_sum (fun w _=>Nat.zero_le (g.deficit w)) (Finset.mem_univ v)))
      left
      simp only [hz,Finset.sum_const_zero,Nat.zero_add]
      rw [graphExcess_iso e]
      omega

theorem componentFiniteReferenceBudget_mono_iso (g:DeficientGraph V d)(h:DeficientGraph W d)
    (e:h.graph≃g g.graph)(hδ:∀v,h.deficit v≤g.deficit (e v))
    (hb:g.ComponentFiniteReferenceBudget):h.ComponentFiniteReferenceBudget:=by
  intro c
  let c':=e.connectedComponentEquiv c
  let φ:=graphIsoComponentIso e c
  exact (g.restrict c'.supp).finiteReferenceBudget_mono_iso (h.restrict c.supp) φ
    (fun v=>hδ v.val) (hb c')

end DeficientGraph
end LocalLaw
