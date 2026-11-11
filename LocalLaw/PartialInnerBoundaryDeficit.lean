import LocalLaw.PartialInnerRestoration
import LocalLaw.PartialInnerAmbient
import LocalLaw.PartialDeficitRestoration

/-! At an accepted A root the partial-inner deficit is precisely the L mask. -/
noncomputable section
namespace LocalLaw
local instance partialInnerBoundaryDeficitDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

omit [Fintype ι] in
theorem partial_inner_boundary_deficit (g:RegularGraph N d)
    (T:Set (Fin N))(labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Fin N)):
    let s:=g.admissibleState T labels samples
    let H:=(g.deficient.restrict S).delete (s.retainedInnerSet S)
    ∀a:s.partialBoundaryMask selector (s.fullSliceOutside S),
      H.deficit (s.partialInnerBoundaryEmbedding selector S a)=
        if a.val∈s.retainedInnerLabels selector S then 1 else 0:=by
  dsimp only
  let s:=g.admissibleState T labels samples
  let Tm:=s.retainedInnerSet S
  let H:=(g.deficient.restrict S).delete Tm
  let K:=s.fullSliceOutside S
  let e:=s.partialInnerBoundaryEmbedding selector S
  intro a
  have hglobal:((g.deficient.delete T).restrict K).deficit (s.partialBoundaryEmbedding selector K a)=1:=
    g.includedEligibleBoundary_deficit_one T labels samples selector K _ ⟨a.val,rfl⟩
  have hpart:=g.deficient.partial_restrictionDeletion_deficit S T Tm (fun _=>Iff.rfl) (e a)
  change ((g.deficient.delete T).restrict K).deficit (s.partialBoundaryEmbedding selector K a)=
    H.deficit (e a)+Nat.card {t:T//t.val∉S∧g.graph.Adj t.val (e a).val.val} at hpart
  rw [hglobal] at hpart
  by_cases hL:a.val∈s.retainedInnerLabels selector S
  · rw [if_pos hL]
    change H.deficit (e a)=1
    have hp:=g.partial_inner_boundary_restoration_positive T labels samples selector S a hL
    change 0<H.deficit (e a) at hp
    omega
  · rw [if_neg hL]
    change H.deficit (e a)=0
    let l:T:=⟨(s.quad a.val.val).a,sampledSwitching_root_mem s.graph T s.samples (s.boundary a.val.val)⟩
    have hab:g.graph.Adj l.val (e a).val.val:=
      (sampledSwitching_admissible s.graph T selector s.samples (s.boundary a.val.val)
        a.val.property.1 a.val.property.2).old_ab
    haveI:Nonempty {t:T//t.val∉S∧g.graph.Adj t.val (e a).val.val}:=⟨⟨l,hL,hab⟩⟩
    have hp:0<Nat.card {t:T//t.val∉S∧g.graph.Adj t.val (e a).val.val}:=Nat.card_pos
    omega

end RegularGraph
end LocalLaw
