import LocalLaw.OmittedRestoredUniformDecay

/-! # Uniform actual source decay after local selected-B deletion

Both source inputs are proved factories. The resulting common-metric
bound has fixed coefficients and applies to every local core target pair.
-/

open Filter
noncomputable section
namespace LocalLaw
namespace RegularGraph
theorem eventually_source_omitted_restored_decay (a b d : ℕ)(c β B C1 : ℝ)
    (ha : 12≤a)(hb : 25*a≤b)(hd : 3≤d)(hc : 0<c)(hβ : 0<β)(hβc : β≤c/32)(hC1 : 1≤C1) :
    ∀ᶠ N:ℕ in atTop,∀(g : RegularGraph N d)(o : Fin N)(z q : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → 0≤q.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀{ι:Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : ((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector := logarithmicRadius (c/4) d N/4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T labels samples
      ∀S:Set (Tᶜ:Set (Fin N)),S⊆s.twoTargetEndpointVertices selector r x y →
        g.OmittedRestoredDecayControlled T labels samples selector S q z B C1
          (omittedCompletionObservationLogCap d β) (Real.log (N:ℝ))
          (graphPaperError a d N (logarithmicRadius β d N) z) := by
  let A := omittedCompletionObservationLogCap d β
  have hA0 : 0≤sourceObservationLogCap d β := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hApart : 0≤sourcePartialObservationLogCap d β := by unfold sourcePartialObservationLogCap;positivity
  have hA : 0≤A := by dsimp only [A,omittedCompletionObservationLogCap];positivity
  filter_upwards [eventually_source_omitted_leaf_inputs a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_omitted_kept_control a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_formal_diagonal_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1]
    with N hinputs hcontrol hformal hnum
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  intro S hS
  have hi := hinputs g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS
  have hc' := hcontrol g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS
  have hf := hformal z q hz hzB hfloor hprior
  have num := hnum z hz hfloor
  exact g.actual_omitted_restored_uniform_decay hd _ labels samples _ _ S q z B C1 A
    (Real.log (N:ℝ)) _ hz hq hf.2.1 hf.2.2.2.2.2 num.log_one num.error_nonnegative hA hi hc'

end RegularGraph
end LocalLaw
