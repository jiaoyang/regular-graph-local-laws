import LocalLaw.PartialInnerModelUpdate
import LocalLaw.SubsetDeficitRestoration

/-! Genuine A-restoration only when its inner mate was retained. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialInnerRestorationDecidable (p:Prop):Decidable p:=Classical.propDecidable p
set_option maxHeartbeats 3000000
namespace LabelledResamplingState
variable {V:Type}{T:Set V}{ι:Type}

def partialInnerBoundaryEmbedding (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set V):
    s.partialBoundaryMask selector (s.fullSliceOutside S)↪((s.retainedInnerSet S)ᶜ:Set S) where
  toFun a:=s.partialInnerDeletedEmbedding selector S (Sum.inl a)
  inj' _a _b hab:=Sum.inl_injective ((s.partialInnerDeletedEmbedding selector S).injective hab)

def partialInnerRestoreLabels (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set V):
    Set (s.partialBoundaryMask selector (s.fullSliceOutside S)):=
  {a|a.val∈s.retainedInnerLabels selector S}

end LabelledResamplingState
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

omit [Fintype ι] in
theorem partial_inner_boundary_restoration_positive (g:RegularGraph N d)
    (T:Set (Fin N))(labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Fin N)):
    let s:=g.admissibleState T labels samples
    let H:=(g.deficient.restrict S).delete (s.retainedInnerSet S)
    ∀a∈s.partialInnerRestoreLabels selector S,
      0<H.deficit (s.partialInnerBoundaryEmbedding selector S a):=by
  dsimp only
  let s:=g.admissibleState T labels samples
  let Tm:=s.retainedInnerSet S
  let H:=(g.deficient.restrict S).delete Tm
  intro a ha
  let l:Tm:=⟨⟨(s.quad a.val.val).a,ha⟩,
    sampledSwitching_root_mem s.graph T s.samples (s.boundary a.val.val)⟩
  let e:=s.partialInnerBoundaryEmbedding selector S
  have hab:g.graph.Adj l.val.val (e a).val.val:=by
    change s.graph.Adj (s.quad a.val.val).a (s.quad a.val.val).b
    exact (sampledSwitching_admissible s.graph T selector s.samples (s.boundary a.val.val)
      a.val.property.1 a.val.property.2).old_ab
  haveI:Nonempty {t:Tm//(g.graph.induce S).Adj t.val (e a).val}:=⟨⟨l,hab⟩⟩
  have hc:0<Nat.card {t:Tm//(g.graph.induce S).Adj t.val (e a).val}:=Nat.card_pos
  rw [(g.deficient.restrict S).delete_deficit_eq_removed_neighbors]
  exact Nat.lt_of_lt_of_le hc (Nat.le_add_left _ _)

omit [Fintype ι] in
theorem partial_inner_boundary_separated (g:RegularGraph N d)
    (T:Set (Fin N))(labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Fin N)):
    let s:=g.admissibleState T labels samples
    let H:=(g.deficient.restrict S).delete (s.retainedInnerSet S)
    let e:=s.partialInnerBoundaryEmbedding selector S
    ∀a b,a≠b→(selector:ℕ∞)≤H.graph.edist (e a) (e b):=by
  dsimp only
  let s:=g.admissibleState T labels samples
  let H:=(g.deficient.restrict S).delete (s.retainedInnerSet S)
  let e:=s.partialInnerBoundaryEmbedding selector S
  let f:H.graph→g outsideGraph g.graph T:=
    { toFun:=fun v=>⟨v.val.val,v.property⟩
      map_rel':=fun h=>h }
  intro a b hab
  have hne:a.val≠b.val:=fun he=>hab (Subtype.ext he)
  have hfar:=s.admissibleTripleVertex_separated selector a.val b.val hne 0 0
  have hs:(selector:ℕ∞)<(outsideGraph g.graph T).edist (f (e a)) (f (e b)):=by
    change (selector:ℕ∞)<(outsideGraph s.graph T).edist
      (s.admissibleBoundaryVertex selector a.val) (s.admissibleBoundaryVertex selector b.val) at hfar
    exact hfar
  exact hs.le.trans (graphHom_edist_le f _ _)

theorem partial_inner_boundary_restored_rows (g:RegularGraph N d)(hd:3≤d)
    (T:Set (Fin N))(labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Fin N))(q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(R:ℕ):
    let s:=g.admissibleState T labels samples
    let H:=(g.deficient.restrict S).delete (s.retainedInnerSet S)
    let e:=s.partialInnerBoundaryEmbedding selector S
    let A:=s.partialBoundaryMask selector (s.fullSliceOutside S)
    let P:=(H.extensionGreen q z).submatrix e e
    let K:=P⁻¹-partialLMaskRestoration A (s.retainedInnerLabels selector S) q (treeEdgeWeight d)
    H.ComponentFiniteReferenceBudget→(∀x y,H.graph.dist x y≤R)→
    ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2→
    (Fintype.card A:ℝ)*physicalTransfer d z^selector≤1→
    IsUnit K∧(∀a,∑b,‖K⁻¹ a b‖≤4*finiteExtraReferenceConstant d)∧
      (∀b,∑a,‖K⁻¹ a b‖≤4*finiteExtraReferenceConstant d):=by
  dsimp only
  let s:=g.admissibleState T labels samples
  let H:=(g.deficient.restrict S).delete (s.retainedInnerSet S)
  let e:=s.partialInnerBoundaryEmbedding selector S
  let A:=s.partialBoundaryMask selector (s.fullSliceOutside S)
  let F:=s.partialInnerRestoreLabels selector S
  intro hb hR small hcount
  have hh:=H.subsetDeficitRestoration_embedding_rows hd hb e F
    (g.partial_inner_boundary_restoration_positive T labels samples selector S) selector
    (g.partial_inner_boundary_separated T labels samples selector S) q z hz hq R hR small hcount
  dsimp only at hh
  have he:q•Matrix.diagonal (fun a:A=>if a∈F then ((1/((d:ℝ)-1):ℝ):ℂ) else 0)=
      partialLMaskRestoration A (s.retainedInnerLabels selector S) q (treeEdgeWeight d):=by
    ext a b
    by_cases hab:a=b
    · subst b
      simp only [Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply_eq,partialLMaskRestoration]
      change q*(if a.val∈s.retainedInnerLabels selector S then ((1/((d:ℝ)-1):ℝ):ℂ) else 0)=
        if a.val∈s.retainedInnerLabels selector S then q*treeEdgeWeight d^2 else 0
      by_cases ha:a.val∈s.retainedInnerLabels selector S
      · simp only [ha,if_true,treeEdgeWeight_sq d hd]
        push_cast
        ring
      · simp [ha]
    · simp only [Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply,partialLMaskRestoration,hab,if_false,mul_zero]
  rw [he] at hh
  exact hh

end RegularGraph
end LocalLaw
