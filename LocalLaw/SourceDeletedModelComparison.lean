import LocalLaw.SourceInnerStarPrime
import LocalLaw.SourceOuterFirstDeletion
import LocalLaw.SourceLocalOuterFirstDeletion

/-! # Actual switched common model versus the literal deleted pair model -/

open Filter
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance sourceDeletedModelComparisonDecidable (p:Prop):Decidable p:=Classical.propDecidable p
local instance (priority := 2000) sourceDeletedModelRangeDecidable {L W:Type}(a:L↪W) :
    DecidablePred (fun v:W=>v∈Set.range a):=fun _=>Classical.propDecidable _

def sourceDeletedModelErrorConstant (d:ℕ)(β B C1:ℝ):ℝ:=sourceInnerStarPrimeConstant d β B C1+2

namespace RegularGraph

theorem eventually_source_deleted_model_comparison (a b d:ℕ)(c β Bcap C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hC1:1≤C1) :
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z q:ℂ),
      0<z.im→‖z‖≤Bcap→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z)→
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d)→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      let S:=s.twoTargetEndpointVertices selector r x y
      let xl:=twoBallLeft (outsideGraph g.graph T) (s.endpointModelVertices selector r) x y r
      let yl:=twoBallRight (outsideGraph g.graph T) (s.endpointModelVertices selector r) x y r
      let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
      ‖(new.restrict S).extensionGreen q z xl yl-new.P r z q x y‖≤
        sourceDeletedModelErrorConstant d β Bcap C1*g.sourcePrime a (logarithmicRadius β d N) z := by
  filter_upwards [eventually_source_outer_first_deletion a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_local_outer_first_deletion a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_inner_star_prime a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc]
    with N houter hlocal hstar hradius
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  have hr:1≤r:=hradius.2.1
  let S₀:=s.twoTargetEndpointVertices selector r x y
  let S₁:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
  let O:=s.outerFirstSet selector r x y
  let I:=s.innerStarDeletedCore selector r x y
  let J:=s.innerFirstSet selector r x y
  let layout:=s.innerStarLayout selector r hr x y
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  let M₀:=(new.restrict S₀).delete {v:S₀|v.val∈O}
  let M₁:=(new.restrict S₁).delete {v:S₁|v.val∈O}
  let aJ:=restrictedStarInner S₀ O J layout.inner_left layout.inner_not_outer
  let bJ:=restrictedStarInner S₁ O J layout.inner_right layout.inner_not_outer
  let eI:=restrictedStarCore S₀ O I J layout.core_left layout.core_not_outer layout.inner_left layout.inner_not_outer layout.core_not_inner
  let fI:=restrictedStarCore S₁ O I J layout.core_right layout.core_not_outer layout.inner_right layout.inner_not_outer layout.core_not_inner
  let E:=embeddedStarEmbedding aJ eI
  let F:=embeddedStarEmbedding bJ fI
  let cover:=s.innerStarDeletedCore_targets selector r x y
  let tx:=starTargetIndex I J x cover.1
  let ty:=starTargetIndex I J y cover.2
  let xl:S₀:=twoBallLeft (outsideGraph g.graph T) (s.endpointModelVertices selector r) x y r
  let yl:S₀:=twoBallRight (outsideGraph g.graph T) (s.endpointModelVertices selector r) x y r
  let pl:S₁:=pairBallLeft new.graph x y r
  let pr:S₁:=pairBallRight new.graph x y r
  have hEx:(E tx).val.val=x:=restrictedStarTarget_value S₀ O I J layout.core_left layout.core_not_outer
    layout.inner_left layout.inner_not_outer layout.core_not_inner x cover.1
  have hEy:(E ty).val.val=y:=restrictedStarTarget_value S₀ O I J layout.core_left layout.core_not_outer
    layout.inner_left layout.inner_not_outer layout.core_not_inner y cover.2
  have hFx:(F tx).val.val=x:=restrictedStarTarget_value S₁ O I J layout.core_right layout.core_not_outer
    layout.inner_right layout.inner_not_outer layout.core_not_inner x cover.1
  have hFy:(F ty).val.val=y:=restrictedStarTarget_value S₁ O I J layout.core_right layout.core_not_outer
    layout.inner_right layout.inner_not_outer layout.core_not_inner y cover.2
  have hEx':(E tx).val=xl:=Subtype.ext hEx
  have hEy':(E ty).val=yl:=Subtype.ext hEy
  have hFx':(F tx).val=pl:=Subtype.ext hFx
  have hFy':(F ty).val=pr:=Subtype.ext hFy
  have h₀:=houter g o z q hz hzB hfloor hq hprior hballs labels samples x y (E tx) (E ty) hEx hEy
  have h₁:=hlocal g o z q hz hzB hfloor hq hprior hballs labels samples x y (F tx) (F ty) hFx hFy
  rw[hEx',hEy'] at h₀
  rw[hFx',hFy'] at h₁
  have hs:=hstar g o z q hz hzB hfloor hq hprior hballs labels samples x y hr
  change ‖M₀.extensionGreen q z (E tx) (E ty)-M₁.extensionGreen q z (F tx) (F ty)‖≤
    sourceInnerStarPrimeConstant d β Bcap C1*g.sourcePrime a (logarithmicRadius β d N) z at hs
  have h₁rev:‖M₁.extensionGreen q z (F tx) (F ty)-(new.restrict S₁).extensionGreen q z pl pr‖≤
      g.sourcePrime a (logarithmicRadius β d N) z:=by
    rw[norm_sub_rev]
    exact h₁
  change ‖(new.restrict S₀).extensionGreen q z xl yl-(new.restrict S₁).extensionGreen q z pl pr‖≤_
  have ht:=norm_sub_le_norm_sub_add_norm_sub
    ((new.restrict S₀).extensionGreen q z xl yl)
    (M₀.extensionGreen q z (E tx) (E ty))
    ((new.restrict S₁).extensionGreen q z pl pr)
  have ht':=norm_sub_le_norm_sub_add_norm_sub
    (M₀.extensionGreen q z (E tx) (E ty))
    (M₁.extensionGreen q z (F tx) (F ty))
    ((new.restrict S₁).extensionGreen q z pl pr)
  exact (ht.trans (add_le_add h₀ (ht'.trans (add_le_add hs h₁rev)))).trans_eq (by
    unfold sourceDeletedModelErrorConstant
    ring)

end RegularGraph
end LocalLaw
