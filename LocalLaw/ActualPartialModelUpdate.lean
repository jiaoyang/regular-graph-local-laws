import LocalLaw.PartialSurgeryCoupling
import LocalLaw.SourceCavityTreeIdentity

/-! # Genuine inverse updates for an arbitrary partially retained region

Crossing modified edges contribute the diagonal charges proved in
PartialSwitchCharges. Thus all model changes are supported on the included
accepted exterior endpoints, without a capture or new reference-class input.
-/

noncomputable section
namespace LocalLaw
local instance actualPartialModelUpdateDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem partial_model_difference_coupling (g:RegularGraph N d) (hd:3≤d)
    (T:Set (Fin N)) (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector:ℕ) (S:Set (Tᶜ:Set (Fin N))) (q z:ℂ) :
    let s:=g.admissibleState T labels samples
    let old:=(g.deficient.delete T).restrict S
    let new:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
    (new.extensionMatrix q z-old.extensionMatrix q z).submatrix
      (s.partialEndpointEmbedding selector S) (s.partialEndpointEmbedding selector S)=
      s.partialActualCoupling selector S q (treeEdgeWeight d) := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let old:=g.deficient.delete T
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  let e:=s.partialEndpointEmbedding selector S
  have hh:=old.restrict_extensionMatrix_difference_partial new S
    (g.deleted_degree_deficit_saturated T)
    ((g.labelledResampledGraph T labels samples selector).deleted_degree_deficit_saturated T) q z
  change ((new.restrict S).extensionMatrix q z-(old.restrict S).extensionMatrix q z).submatrix e e=_
  rw [hh]
  have hphysical (x y:(Tᶜ:Set (Fin N))) : (new.H-old.H) x y=
      treeEdgeWeight d*((if (outsideGraph (s.fullResample selector).graph T).Adj x y then 1 else 0)-
        (if (outsideGraph s.graph T).Adj x y then 1 else 0)) := by
    have hn:new.graph=outsideGraph (s.fullResample selector).graph T:=rfl
    have ho:old.graph=outsideGraph s.graph T:=rfl
    simp only [DeficientGraph.H,normalizedAdjacency,Matrix.sub_apply,Matrix.smul_apply,
      smul_eq_mul,SimpleGraph.adjMatrix_apply,treeEdgeWeight,hn,ho]
    ring
  ext u v
  have hc:(old.crossingChargeDifference new S (e u):ℂ)=
      s.outsideCrossingDelta selector S (e u).val/(((d:ℝ)-1:ℝ):ℂ) :=
    old.crossingChargeDifference_cast_sum new S (e u)
  have hcast:(((d:ℝ)-1:ℝ):ℂ)=(d:ℂ)-1:=by push_cast;rfl
  have hsq:=treeEdgeWeight_sq d hd
  change (new.H-old.H) (e u).val (e v).val-
    q*(if e u=e v then (old.crossingChargeDifference new S (e u):ℂ) else 0)=
    treeEdgeWeight d*((if (outsideGraph (s.fullResample selector).graph T).Adj (e u).val (e v).val then 1 else 0)-
      (if (outsideGraph s.graph T).Adj (e u).val (e v).val then 1 else 0))-
      q*treeEdgeWeight d^2*(if u=v then s.outsideCrossingDelta selector S (e u).val else 0)
  rw [hphysical]
  have he:(e u=e v)↔u=v:=e.injective.eq_iff
  simp only [he]
  by_cases huv:u=v
  · subst v
    simp only [if_true]
    rw [hc,hcast,hsq]
    ring
  · simp only [huv,if_false,mul_zero,sub_zero]


theorem partial_model_difference_supported (g:RegularGraph N d)
    (T:Set (Fin N)) (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector:ℕ) (S:Set (Tᶜ:Set (Fin N))) (q z:ℂ) :
    let s:=g.admissibleState T labels samples
    let old:=(g.deficient.delete T).restrict S
    let new:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
    ∀ x y:S,x∉Set.range (s.partialEndpointEmbedding selector S)∨
      y∉Set.range (s.partialEndpointEmbedding selector S)→
        (new.extensionMatrix q z-old.extensionMatrix q z) x y=0 := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let old:=g.deficient.delete T
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  let e:=s.partialEndpointEmbedding selector S
  have haway (x:S) (hx:x∉Set.range e) : x.val∉s.fullResampleOutsideEndpoints selector := by
    rintro ⟨i,hi,hxi⟩
    apply hx
    apply (s.partialEndpointEmbedding_range selector S x).mpr
    exact ⟨⟨i,hi⟩,hxi⟩
  have hh:=old.restrict_extensionMatrix_difference_partial new S
    (g.deleted_degree_deficit_saturated T)
    ((g.labelledResampledGraph T labels samples selector).deleted_degree_deficit_saturated T) q z
  intro x y hxy
  rw [hh]
  have hp:(new.H-old.H) x.val y.val=0:=s.fullResample_outside_difference_supported selector d x.val y.val
    (hxy.imp (haway x) (haway y))
  simp only [Matrix.sub_apply,Matrix.submatrix_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.diagonal_apply,hp,zero_sub]
  by_cases he:x=y
  · subst y
    have hx:x.val∉s.fullResampleOutsideEndpoints selector:=haway x (hxy.elim id id)
    have hc:old.crossingChargeDifference new S x=0:=
      old.crossingChargeDifference_eq_zero_of_agreement new S x (fun w=>
        (s.fullResample_outside_adj_of_away_left selector x.val w.val hx).symm)
    simp [hc]
  · simp [he]

theorem partial_model_endpoint_updates (g:RegularGraph N d) (hd:3≤d)
    (T:Set (Fin N)) (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector:ℕ) (S:Set (Tᶜ:Set (Fin N))) (q z:ℂ) (hz:0<z.im) (hq:0≤q.im) :
    let s:=g.admissibleState T labels samples
    let e:=s.partialEndpointEmbedding selector S
    let R:=((g.deficient.delete T).restrict S).extensionGreen q z
    let U:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).extensionGreen q z
    let W:=s.partialActualCoupling selector S q (treeEdgeWeight d)
    (U.submatrix e e+R.submatrix e e*W*U.submatrix e e=R.submatrix e e)∧
      (U.submatrix e e+U.submatrix e e*W*R.submatrix e e=R.submatrix e e) := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let old:=(g.deficient.delete T).restrict S
  let new:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
  have hu:=inverse_embedded_finite_rank_updates (old.extensionMatrix q z) (new.extensionMatrix q z)
    (old.extensionMatrix_isUnit hd q z hz hq) (new.extensionMatrix_isUnit hd q z hz hq)
    (s.partialEndpointEmbedding selector S)
    (g.partial_model_difference_supported T labels samples selector S q z)
  dsimp only at hu
  rw [g.partial_model_difference_coupling hd T labels samples selector S q z] at hu
  exact hu

end RegularGraph
end LocalLaw
