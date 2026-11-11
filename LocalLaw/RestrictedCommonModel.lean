import LocalLaw.OmittedLeafModels
import LocalLaw.SelectedCommonCapture

/-! # Actual old and new augmented models agree after all selected B deletion

Containing every selected B vertex makes restriction commute with the full
physical deletion, including inherited deficits. No reference-class or
inverse comparison premise is involved.
-/

noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance restrictedCommonModelDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

theorem restricted_selectedFirst_deletion_eq (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(A:Set (Tᶜ:Set (Fin N)))
    (hA:(g.admissibleState T labels samples).selectedFirstSet selector⊆A) :
    let B:=(g.admissibleState T labels samples).partialFirstRemovedSet selector A
    (((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict A).delete B=
      (((g.deficient.delete T).restrict A).delete B) := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let W:=s.selectedFirstSet selector
  let B:=s.partialFirstRemovedSet selector A
  let old:=g.deficient.delete T
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  have hglobal:=g.labelledResampled_delete_selectedFirst_eq T labels samples selector
  change new.delete W=old.delete W at hglobal
  apply DeficientGraph.eq_of_graph_and_deficit_eq
  · ext u v
    exact s.fullResample_without_selectedFirst_adj selector
      (s.selectedCommonEmbedding selector A u) (s.selectedCommonEmbedding selector A v)
  · funext v
    have hn:=new.restrictionDeletion_deficit A W B (fun _=>Iff.rfl) hA v
    have ho:=old.restrictionDeletion_deficit A W B (fun _=>Iff.rfl) hA v
    rw [hglobal] at hn
    exact hn.trans ho.symm

end RegularGraph
end LocalLaw
