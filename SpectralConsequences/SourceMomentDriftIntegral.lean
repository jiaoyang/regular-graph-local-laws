import SpectralConsequences.SourceTraceConditionalKernel
import SpectralConsequences.SourceCavityKernelBudget
import SpectralConsequences.SourceMomentTargetCaps
import SpectralConsequences.SourceMomentSupportCaps
import SpectralConsequences.BallConditionalException

/-! Actual drift integral for BOTH Section7 observables on the genuine
reversible labelled-ball space, with an all-polynomial auxiliary loss. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceMomentDriftIntegralDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def momentSwitchDrift (N d:ℕ)(cavity:Bool)(o:Fin N)(ell selector:ℕ)(z:ℂ)
    (ω:BallLabelledSpace N d):ℂ:=
  momentLocalObservable cavity (ballLabelledProject (ballLabelledPermutation N d selector ω)) o z-
    momentRecursionTarget cavity (ballLabelledProject ω) ell z

def sourceMomentDriftCap (d:ℕ):ℝ:=2*finiteExtraReferenceConstant d+6

namespace RegularGraph

theorem eventually_source_moment_conditional_drift_cap (a b d:ℕ)(c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hB:0≤B):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→
      momentSourceEvent N d a c β z g→momentTreeEvent N d o c g→∀cavity:Bool,
      let ell:=actualCavityDepth a d N z-1
      ‖ballLabelledConditionalMean N d o ell
        (momentSwitchDrift N d cavity o ell (logarithmicRadius (c/4) d N/4) z) g‖≤sourceMomentDriftCap d:=by
  have hC:0≤sourceMomentDriftCap d:=by
    have hh:=finiteExtraReferenceConstant_ge_one d hd
    dsimp only [sourceMomentDriftCap];positivity
  filter_upwards [eventually_source_trace_all_sampling_cap a b d c β B ha hb hd hc hβ hβc hB,
    eventually_source_cavity_all_sampling_cap a b d c β B ha hb hd hc hβ hβc hB,
    eventually_source_moment_target_cap a b d β ha hb hd hβ] with N htrace hcavity htarget
  intro g o z hz hfloor hzB hold htree cavity
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  apply ballLabelledConditionalMean_norm_bound N d o ell _ g (sourceMomentDriftCap d) hC
  intro labels S
  simp only [momentSwitchDrift,canonicalBallLabelledState_project,canonicalBallLabelledState_permutation_project]
  have ht:=htarget g z hz hfloor _ _ _ hold cavity
  have hn:‖momentLocalObservable cavity
      (g.labelledResampledGraph (graphBallVertices g.graph o ell) labels S (logarithmicRadius (c/4) d N/4)) o z‖≤
      2*finiteExtraReferenceConstant d+1:=by
    cases cavity with
    | false => exact (htrace g o z hz hfloor hzB _ hold htree labels S).2
    | true => exact hcavity g o z hz hfloor hzB _ hold htree labels S
  exact ((norm_sub_le _ _).trans (add_le_add hn ht)).trans_eq (by dsimp only [sourceMomentDriftCap];ring)

theorem eventually_source_moment_drift_integral (a b d p D:ℕ)(c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hc1:c≤1/16)(hβ:0<β)(hβc:β≤c/32)(hB:0≤B):
    ∀ᶠ N:ℕ in Filter.atTop,∀z:ℂ,0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→
      ∀(cavity:Bool)(o:Fin N),
      let ell:=actualCavityDepth a d N z-1
      let selector:=logarithmicRadius (c/4) d N/4
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      ‖finiteExpectation (ballLabelledWeight N d o ell) (fun ω=>
        if momentSourceEvent N d a c β z (ballLabelledProject ω)∧momentTreeEvent N d o c (ballLabelledProject ω)
        then momentSwitchDrift N d cavity o ell selector z ω*
          complexMomentTest p (momentResidual cavity (ballLabelledProject ω) ell z) else 0)‖≤
        (sourceTraceDriftConstant d β B*Real.log (N:ℝ)^(6*a+7)*ε^2)*
          (∑g:LocalLaw.RegularGraph N d,if momentSourceEvent N d a c β z g
            then LocalLaw.RegularGraph.weight g*‖momentResidual cavity g ell z‖^(2*p-1) else 0)+
        sourceMomentDriftCap d*(sourceMomentResidualCap d)^(2*p-1)/(N:ℝ)^D:=by
  have hC:0≤sourceMomentDriftCap d:=by
    have hh:=finiteExtraReferenceConstant_ge_one d hd
    dsimp only [sourceMomentDriftCap];positivity
  have hM:0≤sourceMomentResidualCap d:=by
    have hh:=finiteReferenceConstant_ge_one d hd
    dsimp only [sourceMomentResidualCap,sourceGreenEntryCap];positivity
  filter_upwards [eventually_source_trace_conditional_kernel a b d c β B ha hb hd hc hc1 hβ hβc hB,
    eventually_source_cavity_kernel_quadratic a b d c β B ha hb hd hc hc1 hβ hβc hB,
    eventually_source_moment_conditional_drift_cap a b d c β B ha hb hd hc hβ hβc hB,
    eventually_source_moment_support_caps a b d c β B ha hb hd hc hβ hβc hB,
    eventually_largeTreeCountAux_failure d D (4*c) (7*c) hd (by positivity) (by linarith),
    eventually_log_ge_nat 1] with N htrace hcavity hcap hsupport haux hlog
  intro z hz hfloor hzB cavity o
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let selector:=logarithmicRadius (c/4) d N/4
  let Ω:=momentSourceEvent N d a c β z
  let χ:=momentTreeEvent N d o c
  let A:LocalLaw.RegularGraph N d→Prop:=fun g=>Ω g∧χ g
  let Aux:=LargeTreeCountAux (4*c) (7*c) (N:=N) (d:=d)
  let f:=momentSwitchDrift N d cavity o ell selector z
  let test:LocalLaw.RegularGraph N d→ℂ:=fun g=>complexMomentTest p (momentResidual cavity g ell z)
  let E:=sourceTraceDriftConstant d β B*Real.log (N:ℝ)^(6*a+7)*
    (graphPaperError a d N (logarithmicRadius β d N) z)^2
  let M:ℝ:=(sourceMomentResidualCap d)^(2*p-1)
  have hE:0≤E:=by dsimp only [E,sourceTraceDriftConstant];positivity
  have htest:∀g,A g→‖test g‖≤M:=by
    intro g hg
    rw [complexMomentTest_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) ((hsupport z hz hfloor hzB).1 cavity g hg.1) _
  have hgood:∀g,A g→Aux g→‖ballLabelledConditionalMean N d o ell f g‖≤E:=by
    intro g hg hLarge
    cases cavity with
    | false => exact htrace g o z hz hfloor hzB _ hg.1 hg.2 hLarge
    | true => exact hcavity g o z hz hfloor hzB _ hg.1 hg.2 hLarge
  have hbad:∀g,A g→¬Aux g→‖ballLabelledConditionalMean N d o ell f g‖≤sourceMomentDriftCap d:=by
    intro g hg _
    exact hcap g o z hz hfloor hzB hg.1 hg.2 cavity
  have hh:=ball_conditional_test_with_exception N d o ell A Aux f test E (sourceMomentDriftCap d) M
    hE hC (pow_nonneg hM _) hgood hbad htest
  have hNorm:‖finiteExpectation (ballLabelledWeight N d o ell) (fun ω=>
      if momentSourceEvent N d a c β z (ballLabelledProject ω)∧momentTreeEvent N d o c (ballLabelledProject ω)
      then momentSwitchDrift N d cavity o ell selector z ω*
        complexMomentTest p (momentResidual cavity (ballLabelledProject ω) ell z) else 0)‖=
      ‖finiteExpectation (ballLabelledWeight N d o ell) (fun ω=>
        @ite ℂ (A (ballLabelledProject ω)) (ballConditionalExceptionDecidable _)
          (f ω*test (ballLabelledProject ω)) 0)‖:=by
    congr 1
    apply congrArg (finiteExpectation (ballLabelledWeight N d o ell))
    funext ω
    dsimp only [A,Ω,χ,f,test]
    split_ifs <;>rfl
  rw [hNorm]
  apply hh.trans
  have hsum:(∑g:LocalLaw.RegularGraph N d,@ite ℝ (A g) (ballConditionalExceptionDecidable _)
      (LocalLaw.RegularGraph.weight g*‖test g‖) 0)≤
      (∑g:LocalLaw.RegularGraph N d,if Ω g then LocalLaw.RegularGraph.weight g*‖momentResidual cavity g ell z‖^(2*p-1) else 0):=by
    apply Finset.sum_le_sum
    intro g _
    by_cases hg:Ω g
    · by_cases ht:χ g
      · simp only [A,hg,ht,and_self,if_true,complexMomentTest_norm,test]
        exact le_rfl
      · simp only [A,hg,ht,and_false,if_false,if_true]
        exact mul_nonneg (LocalLaw.RegularGraph.weight_nonnegative g) (pow_nonneg (norm_nonneg _) _)
    · simp only [A,hg,false_and,if_false]
      exact le_rfl
  have htail:sourceMomentDriftCap d*M*eventMass (LocalLaw.RegularGraph.weight (N:=N) (d:=d)) (fun g=>¬Aux g)≤
      sourceMomentDriftCap d*M/(N:ℝ)^D:=by
    exact (mul_le_mul_of_nonneg_left haux (mul_nonneg hC (pow_nonneg hM _))).trans_eq (by ring)
  exact add_le_add (mul_le_mul_of_nonneg_left hsum hE) htail

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_source_moment_drift_integral
