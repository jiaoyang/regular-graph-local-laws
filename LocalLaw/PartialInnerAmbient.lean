import LocalLaw.PartialDeletionBoundaryDefect
import LocalLaw.DeficitReduction
import LocalLaw.PartialInnerMasks

/-! An ambient outside model for deletion of only retained inner vertices. -/
noncomputable section
namespace LocalLaw
local instance partialInnerAmbientDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V:Type}[Fintype V]{d:ℕ}

def partialInnerOmittedCharge (g:DeficientGraph V d)(T S:Set V)(v:(Tᶜ:Set V)):ℕ:=
  Nat.card {t:T//t.val∉S∧g.graph.Adj t.val v.val}

theorem partialInnerOmittedCharge_le (g:DeficientGraph V d)(T S:Set V)(v:(Tᶜ:Set V)):
    g.partialInnerOmittedCharge T S v≤(g.delete T).deficit v:=by
  rw [g.delete_deficit_eq_removed_neighbors]
  let f:{t:T//t.val∉S∧g.graph.Adj t.val v.val}→{t:T//g.graph.Adj t.val v.val}:=
    fun t=>⟨t.val,t.property.2⟩
  have hf:Function.Injective f:=by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun t:{t:T//g.graph.Adj t.val v.val}=>t.val) h
  exact (Nat.card_le_card_of_injective f hf).trans (Nat.le_add_left _ _)

def partialInnerAmbient (g:DeficientGraph V d)(T S:Set V):DeficientGraph (Tᶜ:Set V) d:=
  (g.delete T).lowerDeficit (g.partialInnerOmittedCharge T S) (g.partialInnerOmittedCharge_le T S)

theorem partialInnerAmbient_deficit_zero (g:DeficientGraph V d)(T S:Set V)(v:(Tᶜ:Set V))
    (hv:(g.delete T).deficit v=0):(g.partialInnerAmbient T S).deficit v=0:=by
  change (g.delete T).deficit v-g.partialInnerOmittedCharge T S v=0
  rw [hv,Nat.zero_sub]

theorem partialInnerAmbient_restrict_deficit (g:DeficientGraph V d)(T S:Set V)
    (Tm:Set S)(hTm:∀v:S,v∈Tm↔v.val∈T)(v:(Tmᶜ:Set S)):
    ((g.partialInnerAmbient T S).restrict {v:(Tᶜ:Set V)|v.val∈S}).deficit
      ((restrictionDeletionGraphIso g.graph S T Tm hTm) v)=((g.restrict S).delete Tm).deficit v:=by
  change ((g.delete T).restrict _).deficit _-g.partialInnerOmittedCharge T S _= _
  rw [g.partial_restrictionDeletion_deficit S T Tm hTm v]
  exact Nat.add_sub_cancel _ _

theorem partialInnerAmbient_restrict_green [DecidableEq V] (g:DeficientGraph V d)(T S:Set V)
    (Tm:Set S)(hTm:∀v:S,v∈Tm↔v.val∈T)(q z:ℂ):
    (((g.partialInnerAmbient T S).restrict {v:(Tᶜ:Set V)|v.val∈S}).extensionGreen q z).submatrix
      (restrictionDeletionGraphIso g.graph S T Tm hTm) (restrictionDeletionGraphIso g.graph S T Tm hTm)=
      ((g.restrict S).delete Tm).extensionGreen q z:=by
  exact ((g.partialInnerAmbient T S).restrict _).extensionGreen_iso ((g.restrict S).delete Tm)
    (restrictionDeletionGraphIso g.graph S T Tm hTm)
    (fun v=>(g.partialInnerAmbient_restrict_deficit T S Tm hTm v).symm) q z

theorem partialInnerAmbient_restrict_budget (g:DeficientGraph V d)(T S:Set V)
    (Tm:Set S)(hTm:∀v:S,v∈Tm↔v.val∈T)
    (hb:((g.restrict S).delete Tm).ComponentFiniteReferenceBudget):
    ((g.partialInnerAmbient T S).restrict {v:(Tᶜ:Set V)|v.val∈S}).ComponentFiniteReferenceBudget:=by
  let e:=restrictionDeletionGraphIso g.graph S T Tm hTm
  exact ((g.restrict S).delete Tm).componentFiniteReferenceBudget_of_iso
    ((g.partialInnerAmbient T S).restrict _) e.symm
    (fun v=>by
      have hh:=g.partialInnerAmbient_restrict_deficit T S Tm hTm (e.symm v)
      simpa only [e.apply_symm_apply] using hh) hb

end DeficientGraph
end LocalLaw
