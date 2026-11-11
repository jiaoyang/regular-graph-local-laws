import LocalLaw.OmittedLeafCounts
import LocalLaw.ActualOmittedSwitchingPrecision
import LocalLaw.AttachedLeafReferenceBudget

/-! # Actual common-core and completed omitted-slot models

All old lost-edge slots and every added A slot can be attached to the common
core. The complete source charge equals the kept-slot multiplicity.
-/

noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance omittedLeafModelsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

abbrev omittedCommonModel (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N))) :=
  ((g.deficient.delete T).delete ((g.admissibleState T labels samples).selectedFirstSet selector)).restrict
    {v : (((g.admissibleState T labels samples).selectedFirstSet selector)ᶜ : Set (Tᶜ : Set (Fin N))) | v.val ∈ S}

omit [Fintype ι] in
theorem omittedCommonModel_deficit (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))
    (v:(g.admissibleState T labels samples).OmittedCore selector S) :
    (g.omittedCommonModel T labels samples selector S).deficit v=
      (g.deficient.delete T).deficit v.val.val+
        Nat.card {b:(g.admissibleState T labels samples).selectedFirstSet selector //
          (outsideGraph g.graph T).Adj b.val v.val.val} := by
  exact (g.deficient.delete T).delete_deficit_eq_removed_neighbors
    ((g.admissibleState T labels samples).selectedFirstSet selector) v.val

theorem omittedExtraMultiplicity_budget (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))
    (v:(g.admissibleState T labels samples).OmittedCore selector S) :
    multiLeafMultiplicity ((g.admissibleState T labels samples).omittedExtraRoot selector S) v≤
      (g.deficient.delete T).deficit v.val.val := by
  let s:=g.admissibleState T labels samples
  apply embedding_multiplicity_le_deficit (s.omittedExtraRoot selector S)
    (fun v:s.OmittedCore selector S=>(g.deficient.delete T).deficit v.val.val)
  intro i
  have hh:=g.eligibleBoundary_deficit_eq_one T labels samples selector i.val
  change 1≤(g.deficient.delete T).deficit (s.admissibleBoundaryVertex selector i.val)
  rw [hh]

theorem omittedAllMate_restore_budget (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))
    (v:(g.admissibleState T labels samples).OmittedCore selector S) :
    multiLeafMultiplicity ((g.admissibleState T labels samples).omittedAllMate selector S) v≤
      (g.omittedCommonModel T labels samples selector S).deficit v := by
  rw [g.omittedCommonModel_deficit,(g.admissibleState T labels samples).omittedAllMultiplicity]
  have hh:=g.omittedExtraMultiplicity_budget T labels samples selector S v
  let n:=Nat.card {b:(g.admissibleState T labels samples).selectedFirstSet selector //
    (outsideGraph g.graph T).Adj b.val v.val.val}
  change n+multiLeafMultiplicity ((g.admissibleState T labels samples).omittedExtraRoot selector S) v≤
    (g.deficient.delete T).deficit v.val.val+n
  omega

theorem omittedKeptMate_restore_budget (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))
    (v:(g.admissibleState T labels samples).OmittedCore selector S) :
    multiLeafMultiplicity ((g.admissibleState T labels samples).omittedAllMate selector S ∘
      (g.admissibleState T labels samples).omittedKeptEmbedding selector S) v≤
      (g.omittedCommonModel T labels samples selector S).deficit v := by
  let s:=g.admissibleState T labels samples
  have hh:multiLeafMultiplicity (s.omittedAllMate selector S ∘s.omittedKeptEmbedding selector S) v≤
      multiLeafMultiplicity (s.omittedAllMate selector S) v := by
    apply Nat.card_le_card_of_injective
      (fun l:{l:s.OmittedOrdinaryLeaves selector S⊕s.OmittedExtraLeaves selector S //
        (s.omittedAllMate selector S ∘s.omittedKeptEmbedding selector S) l=v}=>
          (⟨s.omittedKeptEmbedding selector S l.val,l.property⟩:
            {l:s.OmittedOldLeaves selector S⊕s.OmittedExtraLeaves selector S //s.omittedAllMate selector S l=v}))
    intro l m h
    exact Subtype.ext ((s.omittedKeptEmbedding selector S).injective (congrArg Subtype.val h))
  exact hh.trans (g.omittedAllMate_restore_budget T labels samples selector S v)

end RegularGraph
end LocalLaw
