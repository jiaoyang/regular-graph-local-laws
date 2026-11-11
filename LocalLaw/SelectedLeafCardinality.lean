import LocalLaw.DeletedLeafAugmentation
import LocalLaw.PartialFirstDeletionCaps

/-! # Actual lost-edge leaf counts for retained eligible sample vertices -/
noncomputable section
namespace LocalLaw
local instance selectedLeafCardinalityDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

theorem partialFirst_deletedLeaf_card_bound (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N))) :
    let s:=g.admissibleState T labels samples
    let M:=(g.deficient.delete T).restrict S
    let B:=s.partialFirstRemovedSet selector S
    Nat.card (DeletedLeafIndex M.graph B)≤d*Nat.card (BoundaryOrientedEdge g.graph T) := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let M:=(g.deficient.delete T).restrict S
  let B:=s.partialFirstRemovedSet selector S
  have hB:Nat.card B≤Nat.card ι:=by
    rw [←Nat.card_congr (s.partialFirstRemovalEquiv selector S)]
    exact (Finite.card_subtype_le (fun i:s.AdmissibleSampleIndex selector=>i∈s.partialFirstMask selector S)).trans
      (Finite.card_subtype_le (s.Eligible selector))
  have hcard:=deletedLeafIndex_card_bound M.graph B d M.degree_le
  exact hcard.trans ((Nat.mul_le_mul_right d hB).trans_eq (by rw [Nat.card_congr labels,Nat.mul_comm]))

end RegularGraph
end LocalLaw
