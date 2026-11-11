import LocalLaw.SourcePartialInnerInputs
import LocalLaw.SourcePartialInnerRowParameters
import LocalLaw.SourceFormalEdgeBounds

/-! Constant actual NEW endpoint rows after deleting retained inner vertices.
All old classes, restored deficits, covariance and numerical budgets are derived. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourcePartialInnerEndpointCapsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_partial_inner_endpoint_caps (a b d:ℕ)(c β B C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hC1:1≤C1):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:RegularGraph N d)(o:Fin N)(z q:ℂ),
      0<z.im→‖z‖≤B→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z)→
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d)→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:Fin N)(S:Set (Fin N)),
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      S⊆s.fullTwoTargetVertices selector r x y→
      let e:=s.partialInnerDeletedEmbedding selector S
      let H:=(((g.labelledResampledGraph T labels samples selector).deficient.restrict S).delete (s.retainedInnerSet S)).extensionGreen q z
      (∀i,∑j,‖H (e i) (e j)‖≤sourcePartialEndpointRowCap d)∧
        (∀j,∑i,‖H (e i) (e j)‖≤sourcePartialEndpointRowCap d):=by
  let A:=fullRestrictionLogCap d β
  let D:=sourceFullCovarianceConstant d β B C1
  have hAcaps:=fullRestrictionLogCap_properties d β
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_source_partial_inner_inputs a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_partial_inner_rows_of_covariance a b d β D ha hb hd hβ,
    eventually_source_formal_kernel_bounds a b d c β B C1 A ha hb hd hc hβ hβc hC1 hAcaps.1,
    eventually_source_formal_edge_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,hdepth]
    with N hinputs hrows hformal hedge hdepthN
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y S
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let p:=rationalTreeReference (d-1) q
  intro hSS
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepthN).2
  have inp:=hinputs g o z q hz hzB hfloor hq hprior hballs labels samples x y S hSS
  have hf:=hformal z q hz hzB hfloor hprior
  have he:=hedge z q hz hzB hfloor hprior
  exact hrows g o ell hell labels samples selector z q p hz hfloor hq hf.1 hf.2.1
    hf.2.2.2.1 he.1 hf.2.2.1 he.2 S inp.2.1 inp.2.2.1 inp.1

end RegularGraph
end LocalLaw
