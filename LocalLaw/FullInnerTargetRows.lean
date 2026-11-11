import LocalLaw.SourceFullAugmentedRows
import LocalLaw.FullCutPrecision

/-! # Actual full-model target rows on the complete retained inner set -/

open Filter
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance fullInnerTargetRowsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type} [Fintype V] {T:Set V} {ι:Type}

theorem full_inner_rows_of_augmented_rows (s:LabelledResamplingState V T ι)
    (selector:ℕ)(S:Set V)(hs:1≤selector)(hTS:T⊆S)(G:Matrix S S ℂ)(C:ℝ)
    (u v:S)(hrows:∀i:twoTargetIndexSet (s.fullPartialEmbedding selector S hs) u v,
      ∑j:twoTargetIndexSet (s.fullPartialEmbedding selector S hs) u v,‖G i.val j.val‖≤C) :
    (∑t:T,‖G u (cutInnerEmbedding T S hTS t)‖)≤C := by
  let e:=s.fullPartialEmbedding selector S hs
  let K:=twoTargetIndexSet e u v
  let f:T↪K:=
    {toFun:=fun t=>⟨⟨t.val,hTS t.property⟩,Or.inl ⟨.inl ⟨t.val,hTS t.property,Or.inl t.property⟩,rfl⟩⟩
     inj':=by
       intro t t' h
       exact Subtype.ext (congrArg (fun w:K=>w.val.val) h)}
  let iu:K:=⟨u,Or.inr (Or.inl rfl)⟩
  have hh:(∑t:T,‖G u (f t).val‖)≤∑j:K,‖G u j.val‖:=by
    calc
      _=∑j∈Finset.univ.map f,‖G u j.val‖:=by rw [Finset.sum_map]
      _≤∑j:K,‖G u j.val‖:=Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _=>norm_nonneg _)
  exact hh.trans (hrows iu)

end LabelledResamplingState
namespace RegularGraph

theorem eventually_source_full_inner_target_rows (a b d:ℕ)(c β B C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hC1:1≤C1) :
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z q:ℂ),
      0<z.im→‖z‖≤B→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z)→
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d)→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:Fin N),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      ∀(S:Set (Fin N)),S⊆s.fullTwoTargetVertices selector r x y→∀hTS:T⊆S,
      let M:=(g.labelledResampledGraph T labels samples selector).deficient.restrict S
      ∀u:S,(∑t:T,‖M.extensionGreen q z u (cutInnerEmbedding T S hTS t)‖)≤
        sourceFullAugmentedRowConstant d β*Real.log (N:ℝ)^(2*a-2) := by
  filter_upwards [eventually_source_full_augmented_rows a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_radius_hierarchy a d c β hd hc hβ hβc] with N hrows hradii
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let s:=g.admissibleState T labels samples
  have hs:1≤selector:=by
    have hh:=hradii.2.1
    have hp:=hradii.2.2.1
    dsimp only [selector]
    omega
  intro S hS hTS u
  exact s.full_inner_rows_of_augmented_rows selector S hs hTS _ _ u u
    (hrows g o z q hz hzB hfloor hq hprior hballs labels samples x y hs S hS u u)

end RegularGraph
end LocalLaw
