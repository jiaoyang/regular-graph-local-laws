import LocalLaw.OmittedSwitchingSlots
import LocalLaw.PartialDeletionBoundaryDefect
import LocalLaw.PartialFirstDeletionCaps

/-! # Exact new partial-deletion precision in the physically common graph

Deleting every selected first vertex gives the same global old/new model.
Deleting only selected vertices retained by S misses precisely the ordinary
old slots and added A slots at omitted first vertices. Their complete
diagonal charge is retained below.
-/

noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance actualOmittedPrecisionDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

theorem actual_omitted_switching_precision (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))(q z:ℂ) :
    let s:=g.admissibleState T labels samples
    let W:=s.selectedFirstSet selector
    let B:=s.partialFirstRemovedSet selector S
    let old:=(g.deficient.delete T).delete W
    let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
    let e:=restrictionDeletionGraphIso new.graph S W B (fun _=>Iff.rfl)
    (((old.restrict {v : (Wᶜ : Set (Tᶜ : Set (Fin N))) | v.val ∈ S}).extensionMatrix q z).submatrix e e)=
      ((new.restrict S).delete B).extensionMatrix q z+q•Matrix.diagonal
        (fun v=>(Nat.card (s.OmittedOrdinarySlot selector S v.val.val)+
          Nat.card (s.OmittedAddedSlot selector S v.val.val):ℂ)/((d:ℂ)-1)) := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let W:=s.selectedFirstSet selector
  let B:=s.partialFirstRemovedSet selector S
  let old:=(g.deficient.delete T).delete W
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  have hh:=new.partial_restrictionDeletion_extensionMatrix S W B (fun _=>Iff.rfl) q z
  have hglobal:=g.labelledResampled_delete_selectedFirst_eq T labels samples selector
  change new.delete W=old at hglobal
  rw [hglobal] at hh
  convert hh using 1
  congr 2
  ext v w
  by_cases hvw:v=w
  · subst w
    simp only [Matrix.diagonal_apply_eq]
    congr 2
    have hc:=s.omitted_new_neighbor_count selector S v.val.val
    exact_mod_cast hc.symm
  · simp only [Matrix.diagonal_apply_ne _ hvw]

end RegularGraph
end LocalLaw
