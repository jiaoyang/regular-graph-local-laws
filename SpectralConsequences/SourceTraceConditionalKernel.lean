import SpectralConsequences.SourceTraceDriftBudget
import SpectralConsequences.BallConditionalMaskBounds

/-! The checked trace drift on the actual reversible labelled-ball kernel. -/
open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceTraceConditionalKernelDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def traceSwitchDrift (N d:ℕ)(o:Fin N)(ell selector:ℕ)(z:ℂ)(ω:BallLabelledSpace N d):ℂ:=
  (ballLabelledProject (ballLabelledPermutation N d selector ω)).G z o o-
    (regularRootValue d ell ((ballLabelledProject ω).Q z) z+trivialTraceCorrection N d ell z)

namespace RegularGraph

theorem eventually_source_trace_conditional_kernel (a b d:ℕ)(c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hc1:c≤1/16)(hβ:0<β)(hβc:β≤c/32)(hB:0≤B):
    ∀ᶠ N:ℕ in atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree→LargeTreeCountAux (4*c) (7*c) g→
      let ell:=actualCavityDepth a d N z-1
      ‖ballLabelledConditionalMean N d o ell
        (traceSwitchDrift N d o ell (logarithmicRadius (c/4) d N/4) z) g‖≤
        sourceTraceDriftConstant d β B*Real.log (N:ℝ)^(6*a+7)*
          (graphPaperError a d N (logarithmicRadius β d N) z)^2:=by
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_source_trace_drift_quadratic a b d c β B ha hb hd hc hc1 hβ hβc hB,
    eventually_resampling_ball_budget a d hd,hdepth,eventually_log_ge_nat 1,Filter.eventually_ge_atTop 1]
    with N hdrift hball hdepthN hlog hN
  intro g o z hz hfloor hzB badCount hold htree haux
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let E:=sourceTraceDriftConstant d β B*Real.log (N:ℝ)^(6*a+7)*
    (graphPaperError a d N (logarithmicRadius β d N) z)^2
  have hE:0≤E:=by dsimp only [E,sourceTraceDriftConstant];positivity
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hT:4*Nat.card T≤N:=g.ball_small o ell
    ((Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by omega:0<d+1) hell)).trans hball)
  letI:Nonempty (OutsideOrientedEdge g.graph T):=g.outside_edge_nonempty T (by omega) (by omega) hT
  letI:Nonempty (LocalSamplingFiber g.graph T):=⟨fun _=>Classical.choice inferInstance⟩
  rw [ballLabelledConditionalMean_prod]
  apply finiteComplexMean_norm_bound_nonnegative _ E hE
  intro labels
  simp only [traceSwitchDrift,canonicalBallLabelledState_project,canonicalBallLabelledState_permutation_project]
  rw [finiteComplexMean_sub,finiteComplexMean_const]
  have hh:=hdrift g o z hz hfloor hzB badCount hold htree haux labels
  dsimp only at hh
  rw [←sub_add_eq_sub_sub] at hh
  exact hh

alias eventually_source_trace_kernel_quadratic := eventually_source_trace_conditional_kernel

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_source_trace_conditional_kernel
