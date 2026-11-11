import LocalLaw.AllCentralTreeCavity
import LocalLaw.CentralReferenceIndependence
import LocalLaw.BoundaryBlockPreservation
import LocalLaw.ActualSourceEndpointStability
import LocalLaw.SourceCavityResidual

/-! # Uniform switched boundary control from an original tree neighborhood

This applies to every sampling assignment, including rejected labels. The
exact old/new finite-model boundary block avoids a separate rare-event
resolvent bound in the conditional mean calculation of Section 7.1.
-/
open Filter
noncomputable section
set_option maxHeartbeats 1800000
namespace SpectralConsequences
open LocalLaw
local instance switchedTreeBoundaryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem switched_tree_model_boundary_block (g : LocalLaw.RegularGraph N d)
    (hd : 3 ≤ d) (o : Fin N) (ell r R selector : ℕ)
    (hmargin : ell+r+1 ≤ R) (hTree : (graphBall g.graph o R).IsTree)
    (hsep : 2*r+2 ≤ selector) (hr : r+2 ≤ selector)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (j k : ι) :
    let T := graphBallVertices g.graph o ell
    let s := g.admissibleState T labels samples
    g.sourceEndpointQ T labels samples selector r q z
      (s.endpointFinalBoundaryRoot selector j) (s.endpointFinalBoundaryRoot selector k) =
      if j=k then cavityIterate z q (r+1) else 0 := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T labels samples
  rw [g.sourceEndpoint_boundary_block_preserved hd T labels samples selector r hsep hr q z hz hq]
  change (g.endpointModel T labels samples selector r).extensionGreen q z
    (s.endpointModelKernelEmbedding selector r
      ⟨boundaryOutsideVertex g.graph T (labels j),Or.inl ⟨labels j,rfl⟩⟩)
    (s.endpointModelKernelEmbedding selector r
      ⟨boundaryOutsideVertex g.graph T (labels k),Or.inl ⟨labels k,rfl⟩⟩) = _
  rw [g.endpointModel_boundary_eq_central hd T labels samples selector r hsep q z hz hq]
  have hh := g.tree_central_boundary_block hd o ell r R hmargin hTree (labels j) (labels k) q z hz hq
  dsimp only at hh
  simpa only [labels.injective.eq_iff] using hh

/-- Old source regularity and a genuine old tree ball imply uniform switched
boundary errors for ALL samples/labels. In particular the rejected-label
contribution can be charged by its sampling probability times epsilon-prime. -/
theorem eventually_switched_tree_boundary_cap (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25*a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c/32) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in atTop, ∀ (g : LocalLaw.RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N:ℝ)^b/(N:ℝ) ≤ z.im → ‖z‖ ≤ B → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z →
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector := logarithmicRadius (c/4) d N/4
      let s := g.admissibleState T labels samples
      ∀ j k : ι,
      ‖g.sourceEndpointT T labels samples selector z
        (s.endpointFinalBoundaryRoot selector j) (s.endpointFinalBoundaryRoot selector k) -
        (if j=k then g.Q z else 0)‖ ≤
          (sourceEndpointErrorConstant d C1+1)*g.sourcePrime a (logarithmicRadius β d N) z := by
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [LocalLaw.RegularGraph.eventually_actual_source_endpoint_stability a b d c β B C1
      ha hb hd hc hβ hβc hC1,
    eventually_cavity_residual_le_sourcePrime a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,hdepth]
    with N hstability hresidual hmargin hdepthN
  intro g o z hz hfloor hzB Cq badCount hplus hTree ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let T := graphBallVertices g.graph o ell
  let selector := logarithmicRadius (c/4) d N/4
  let r := effectiveModelRadius a d N β
  let R := logarithmicRadius (c/4) d N
  let s := g.admissibleState T labels samples
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepthN).2
  have htreeMargin : ell+r+1 ≤ R := by dsimp only [ell,r,R];omega
  have hsep : 2*r+2 ≤ selector := by dsimp only [r,selector];omega
  have hr : r+2 ≤ selector := by omega
  have hres := hresidual z (g.Q z) hz hzB hfloor hplus.cavity
  intro j k
  have hh := hstability g o z hz hfloor hzB Cq badCount hplus labels samples
    (s.endpointFinalBoundaryRoot selector j) (s.endpointFinalBoundaryRoot selector k)
  change ‖g.sourceEndpointT T labels samples selector z
    (s.endpointFinalBoundaryRoot selector j) (s.endpointFinalBoundaryRoot selector k)-
    g.sourceEndpointQ T labels samples selector r (g.Q z) z
      (s.endpointFinalBoundaryRoot selector j) (s.endpointFinalBoundaryRoot selector k)‖ ≤ _ at hh
  rw [switched_tree_model_boundary_block g hd o ell r R selector htreeMargin hTree hsep hr
    labels samples (g.Q z) z hz (g.Q_im_nonnegative z hz) j k] at hh
  have hY : ‖(if j=k then cavityIterate z (g.Q z) (r+1) else 0)-
      (if j=k then g.Q z else 0)‖ ≤ g.sourcePrime a (logarithmicRadius β d N) z := by
    by_cases hjk : j=k
    · simpa only [hjk,if_true,norm_sub_rev] using hres
    · simp only [hjk,if_false,sub_self,norm_zero]
      exact (norm_nonneg _).trans hres
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (g.sourceEndpointT T labels samples selector z
      (s.endpointFinalBoundaryRoot selector j) (s.endpointFinalBoundaryRoot selector k))
    (if j=k then cavityIterate z (g.Q z) (r+1) else 0) (if j=k then g.Q z else 0)
  have hfinal := htriangle.trans (add_le_add hh hY)
  convert hfinal using 1
  ring

end RegularGraph
end SpectralConsequences
