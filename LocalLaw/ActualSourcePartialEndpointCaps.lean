import LocalLaw.SourcePartialEndpointCaps
import LocalLaw.SourcePartialGenericInputs
import LocalLaw.SourceFormalEdgeBounds

/-! # Actual switched partial-model row caps for every weak boundary value

The old graph's genuine local excess bound and the scalar weak prior derive
all covariance, restoration and contraction inputs. No reference class for
the switched restriction is assumed. Every subset of the old two-target
augmentation is covered, in particular the actual new pair neighborhood.
-/

open Filter
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance actualSourcePartialEndpointCapsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_partial_endpoint_caps (a b d:ℕ) (c β B C1:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32) (hC1:1≤C1) :
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z q:ℂ),
      0<z.im→‖z‖≤B→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→
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
      ∀S:Set (Tᶜ:Set (Fin N)),S⊆s.twoTargetEndpointVertices selector r x y→
      let e:=s.partialEndpointEmbedding selector S
      let H:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).extensionGreen q z
      (∀i,∑j,‖H (e i) (e j)‖≤sourcePartialEndpointRowCap d)∧
        (∀j,∑i,‖H (e i) (e j)‖≤sourcePartialEndpointRowCap d) := by
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_source_partial_generic_inputs a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_formal_kernel_bounds a b d c β B C1 0 ha hb hd hc hβ hβc hC1 (by norm_num),
    eventually_source_formal_edge_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_partial_endpoint_rows_of_covariance a b d β (sourcePartialCovarianceConstant d β B C1)
      ha hb hd hβ,hdepth] with N hinputs hformal hedge hrows hdepthN
  intro g o z q hz hzB hfloor hqim hprior hballs ι _ labels samples x y
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let p:=rationalTreeReference (d-1) q
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hf:=hformal z q hz hzB hfloor hprior
  have he:=hedge z q hz hzB hfloor hprior
  have hi:=hinputs g o z q hz hzB hfloor hqim hprior hballs labels samples x y
  intro S hS
  have hSinputs:=hi S hS
  exact hrows g o ell hell labels samples selector z q p hz hfloor hqim hf.1 hf.2.1
    hf.2.2.2.1 he.1 hf.2.2.1 he.2 S hSinputs.2.2.1 hSinputs.1

end RegularGraph
end LocalLaw
