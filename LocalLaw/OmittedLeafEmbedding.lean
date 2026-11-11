import LocalLaw.OmittedSwitchingSlots
import LocalLaw.DeletedLeafAugmentation
import LocalLaw.PartialFirstDeletionCaps
import LocalLaw.PairBoundaryDepth
import LocalLaw.EligibleCentralIsolation
import LocalLaw.BoundaryDeficitFibers

/-! # Literal old leaf slots and outer-layer positions of omitted charges

Every ordinary omitted slot embeds into the actual old lost-edge leaf
family. Every new omitted slot, ordinary or added, meets a retained vertex
on the outer layer of both switched target balls. Accepted A vertices have
exactly one old inherited deficit unit, available for their extra leaf.
-/

noncomputable section
namespace LocalLaw
local instance omittedLeafEmbeddingDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type}[Fintype V]{T:Set V}{ι:Type}[Fintype ι]

def ordinaryOmittedLeaf (s:LabelledResamplingState V T ι)(selector:ℕ)
    (A:Set (Tᶜ:Set V))(hA:s.selectedFirstSet selector⊆A)(S:Set (Tᶜ:Set V))
    (v:((s.partialFirstRemovedSet selector A)ᶜ:Set A))
    (i:s.OmittedOrdinarySlot selector S v.val.val) :
    DeletedLeafIndex ((outsideGraph s.graph T).induce A) (s.partialFirstRemovedSet selector A) :=
  ⟨v,⟨⟨⟨s.admissibleSampleVertex selector i.val,hA ⟨i.val,rfl⟩⟩,⟨i.val,rfl⟩⟩,i.property.2.1⟩⟩

def ordinaryOmittedLeafEmbedding (s:LabelledResamplingState V T ι)(selector:ℕ)
    (A:Set (Tᶜ:Set V))(hA:s.selectedFirstSet selector⊆A)(S:Set (Tᶜ:Set V))
    (v:((s.partialFirstRemovedSet selector A)ᶜ:Set A)) :
    s.OmittedOrdinarySlot selector S v.val.val↪
      DeletedLeafIndex ((outsideGraph s.graph T).induce A) (s.partialFirstRemovedSet selector A) where
  toFun:=s.ordinaryOmittedLeaf selector A hA S v
  inj':=by
    intro i j h
    apply Subtype.ext
    apply (s.selectedFirstEmbedding selector).injective
    exact congrArg (fun l:DeletedLeafIndex ((outsideGraph s.graph T).induce A)
      (s.partialFirstRemovedSet selector A)=>l.2.val.val.val) h

omit [Fintype V] [Fintype ι] in
theorem ordinaryOmittedLeaf_mate (s:LabelledResamplingState V T ι)(selector:ℕ)
    (A:Set (Tᶜ:Set V))(hA:s.selectedFirstSet selector⊆A)(S:Set (Tᶜ:Set V))
    (v:((s.partialFirstRemovedSet selector A)ᶜ:Set A))
    (i:s.OmittedOrdinarySlot selector S v.val.val) :
    deletedLeafMate ((outsideGraph s.graph T).induce A) (s.partialFirstRemovedSet selector A)
      (s.ordinaryOmittedLeaf selector A hA S v i)=v := rfl

omit [Fintype V] in
theorem omittedNewIncident_pair_boundary_depth (s:LabelledResamplingState V T ι)(selector r:ℕ)
    (x y v:(Tᶜ:Set V))
    (hv:v∈pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r)
    (i:s.OmittedNewIncident selector
      (pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r) v) :
    (r:ℕ∞)≤(outsideGraph (s.fullResample selector).graph T).edist x v ∧
      (r:ℕ∞)≤(outsideGraph (s.fullResample selector).graph T).edist y v :=
  pair_boundary_inner_edist_lower (outsideGraph (s.fullResample selector).graph T) x y r
    ⟨(v,s.admissibleSampleVertex selector i.val),i.property.2.symm,hv,i.property.1⟩

end LabelledResamplingState
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

omit [Fintype ι] in
theorem eligibleBoundary_deficit_eq_one (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(i:(g.admissibleState T labels samples).AdmissibleSampleIndex selector) :
    (g.deficient.delete T).deficit ((g.admissibleState T labels samples).admissibleBoundaryVertex selector i)=1 := by
  let s:=g.admissibleState T labels samples
  let a:=s.admissibleBoundaryVertex selector i
  let P:={j:ι //(s.boundary j).val.2=a.val}
  let canonical:P:=⟨i.val,rfl⟩
  have huniq:∀j:P,j=canonical:=by
    intro j
    apply Subtype.ext
    by_contra hj
    have hβ:s.boundary j.val≠s.boundary i.val:=fun h=>hj (s.boundary.injective h)
    have hf:=s.eligible_boundary_root_far selector i (s.boundary j.val) hβ
    have he:boundaryOuterEndpoint s.graph T (s.boundary j.val)=a:=Subtype.ext j.property
    change (selector:ℕ∞)<(outsideGraph s.graph T).edist a
      (boundaryOuterEndpoint s.graph T (s.boundary j.val)) at hf
    rw [he,SimpleGraph.edist_self] at hf
    exact not_lt_of_ge (bot_le:(0:ℕ∞)≤selector) hf
  letI:Unique P:=⟨⟨canonical⟩,huniq⟩
  have hcount:Nat.card P=1:=Nat.card_unique
  have hdg:=g.deficient.delete_deficit_eq_removed_neighbors T a
  change (g.deficient.delete T).deficit a=0+Nat.card {t:T //g.graph.Adj t.val a.val} at hdg
  rw [zero_add] at hdg
  rw [hdg]
  exact (Nat.card_congr (s.boundaryNeighborLabelEquiv a)).trans hcount

end RegularGraph
end LocalLaw
