import LocalLaw.SourcePartialWeakCovariance

/-! # Both actual partial covariance models needed by first-stage surgery -/
open Filter
noncomputable section
namespace LocalLaw
namespace RegularGraph

theorem eventually_source_partial_q_covariance_models (a b d : ℕ)(c β B C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hC1:1≤C1) :
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ)(Cq badCount:ℕ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z →
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      let σ:=sourcePartialCovarianceConstant d β B C1*Real.log (N:ℝ)*
        graphPaperError a d N (logarithmicRadius β d N) z
      g.oldPartialQCovarianceBound T labels samples selector
        (pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r) z σ ∧
      g.oldPartialQCovarianceBound T labels samples selector
        (s.twoTargetEndpointVertices selector r x y) z σ := by
  filter_upwards [eventually_source_partial_q_covariance_subsets a b d c β B C1 ha hb hd hc hβ hβc hC1]
    with N hN
  intro g o z Cq badCount hz hzB hfloor hplus hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  have h:=hN g o z Cq badCount hz hzB hfloor hplus hballs labels samples x y
  exact ⟨h _ (s.switched_pairBall_subset_old_augmentation selector r x y),h _ (Set.Subset.refl _)⟩

end RegularGraph
end LocalLaw
