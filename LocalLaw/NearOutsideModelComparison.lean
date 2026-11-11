import LocalLaw.SourceEndpointApproximation
import LocalLaw.ComponentFiniteLipschitz

/-! Near outside comparison on the actual target restriction, with two boundaries. -/
noncomputable section
namespace LocalLaw
local instance nearOutsideModelDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] {d : ℕ}

omit [Fintype I] in
theorem source_restriction_two_boundary_comparison (g : DeficientGraph V d)
    (hd : 3≤d) (S : Set V) (e : I↪S) (r R : ℕ) (z qold qnew : ℂ)
    (hz : 0<z.im) (hold : 0≤qold.im) (hnew : 0≤qnew.im)
    (B C1 ε L A : ℝ) (hB : ‖z‖≤B) (num : SourceObservationBounds d r z B C1 ε L A)
    (hbudget : (g.restrict S).ComponentFiniteReferenceBudget)
    (hdiam : ∀ x y, (g.restrict S).graph.dist x y≤R) (hRlog : (R:ℝ)+1≤A*L)
    (hcapture : ∀ i,graphBallVertices g.graph (e i).val r⊆S)
    (hpriorold : ‖qold-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε)
    (hpriornew : ‖qnew-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε)
    (hpair : ∀ i j, ‖g.G z (e i).val (e j).val-g.P r z qnew (e i).val (e j).val‖≤C1*L^3*ε)
    (i j : I) :
    ‖g.G z (e i).val (e j).val-(g.restrict S).extensionGreen qold z (e i) (e j)‖≤
      2*C1*L^3*ε+(16*finiteExtraReferenceConstant d^2*coreConvolutionConstant (finiteOmega d+1))*‖qold-qnew‖ := by
  have happ:=g.source_endpoint_restriction_approximation hd S e r R z qnew hz hnew B C1 ε L A hB num
    hbudget hdiam hRlog hcapture hpriornew hpair i j
  have scaled (q : ℂ) (hprior : ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε) :
      ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2 := by
    have hp:=hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1 (spectralScale_pos hz)
      num.error_nonnegative num.coefficient_one)
    exact (weak_localization_feedback_budgets d hd z q hz B (C1^2*ε) L A
      (mul_nonneg (sq_nonneg C1) num.error_nonnegative) num.log_one num.log_cap_nonnegative
      num.error_scaled hp R (4*r+1) hRlog num.pair_log num.localization_large).1
  have hlip:=(g.restrict S).componentwise_finite_uniform_lipschitz hd hbudget z qnew qold hz hnew hold R hdiam
    (scaled qnew hpriornew) (scaled qold hpriorold) (e i) (e j)
  have hdiff : ‖(g.restrict S).extensionGreen qnew z (e i) (e j)-
      (g.restrict S).extensionGreen qold z (e i) (e j)‖≤
        (16*finiteExtraReferenceConstant d^2*coreConvolutionConstant (finiteOmega d+1))*‖qold-qnew‖ := by
    simpa only [norm_sub_rev] using hlip
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add happ hdiff)

end DeficientGraph
end LocalLaw
