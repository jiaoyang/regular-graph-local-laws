import SpectralConsequences.SourceMomentSupportCaps
import SpectralConsequences.BallConditionalException
import SpectralConsequences.FiniteWeightedExceptional
import SpectralConsequences.FiniteExitPartition

/-! # Actual exit integrals for both fluctuation-averaging observables

Geometric exits have a genuine conditional polynomial bound. Auxiliary
count failures and switched weak-event failures have every polynomial tail;
they are charged on the true stationary enlarged law.
-/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2600000
namespace SpectralConsequences
open LocalLaw
local instance sourceMomentExitIntegralDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem sourceMomentLocalChangeCap_nonnegative (d:ℕ) (B:ℝ) (hd:3≤d) (hB:0≤B):
    0≤sourceMomentLocalChangeCap d B:=by
  have hCb:=finiteReferenceConstant_ge_one d hd
  have hCe:=finiteExtraReferenceConstant_ge_one d hd
  dsimp only [sourceMomentLocalChangeCap,sourceGreenEntryCap,sourceGreenPivotCap]
  positivity

theorem sourceMomentResidualCap_nonnegative (d:ℕ) (hd:3≤d):0≤sourceMomentResidualCap d:=by
  have hC:=finiteReferenceConstant_ge_one d hd
  dsimp only [sourceMomentResidualCap,sourceGreenEntryCap]
  linarith

theorem eventually_source_moment_exit_integral (a b d D:ℕ) (c β B:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hc1:c≤1/16)
    (hβ:0<β) (hβc:β≤c/32) (hB:2*(d:ℝ)≤B):
    ∀ᶠ N:ℕ in Filter.atTop,∀(z:ℂ),0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→
      let ell:=actualCavityDepth a d N z-1
      let R:=logarithmicRadius (c/4) d N
      let selector:=R/4
      let A:=fun(g:RegularGraph N d)(o:Fin N)=>momentSourceEvent N d a c β z g∧momentTreeEvent N d o c g
      ∀(cavity:Bool)(p:ℕ)(o:Fin N),
      ‖finiteExpectation (ballLabelledWeight N d o ell) (fun ω=>
        if A (ballLabelledProject ω) o ∧
          ¬A (ballLabelledProject (ballLabelledPermutation N d selector ω)) o then
          momentLocalChange N d cavity o selector z ω*
            complexMomentTest p (momentResidual cavity (ballLabelledProject ω) ell z) else 0)‖≤
        (sourceMomentLocalChangeCap d B/(N:ℝ)^(9/32:ℝ))*
          (∑g:RegularGraph N d,if momentSourceEvent N d a c β z g then
            RegularGraph.weight g*‖momentResidual cavity g ell z‖^(2*p-1) else 0)+
        3*sourceMomentLocalChangeCap d B*(sourceMomentResidualCap d)^(2*p-1)/(N:ℝ)^D:=by
  have hB0:0≤B:=by have hh:=(Nat.cast_le (α:=ℝ)).mpr hd;linarith
  have hC:=sourceMomentLocalChangeCap_nonnegative d B hd hB0
  have hM:=sourceMomentResidualCap_nonnegative d hd
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [RegularGraph.eventually_source_moment_geometric_exit a b d c β B ha hb hd hc hc1 hβ hβc hB0,
    RegularGraph.eventually_source_all_sample_local_change_cap a b d c β B ha hb hd hc hβ hβc hB0,
    RegularGraph.eventually_source_moment_support_caps a b d c β B ha hb hd hc hβ hβc hB0,
    eventually_moment_auxiliary_failure d D c hd hc,
    source_point_weak_failure a b d c β B ha hb hd hc (by linarith) hβ hβc hB D,
    eventually_resampling_ball_budget a d hd,hdepth,Filter.eventually_ge_atTop 1]
    with N hgeo hchange hsupport haux hweak hball hdepthN hN
  intro z hz hfloor hzB
  dsimp only
  intro cavity p o
  let ell:=actualCavityDepth a d N z-1
  let R:=logarithmicRadius (c/4) d N
  let selector:=R/4
  let w:=ballLabelledWeight N d o ell
  let Ω:=momentSourceEvent N d a c β z
  let A:RegularGraph N d→Prop:=fun g=>Ω g∧momentTreeEvent N d o c g
  let G:=momentGeometricExit N d o selector R ⌊(N:ℝ)^c⌋₊
  let W:BallLabelledSpace N d→Prop:=fun ω=>momentWeakFailure N d a c β z
    (ballLabelledProject (ballLabelledPermutation N d selector ω))
  let test:RegularGraph N d→ℂ:=fun g=>complexMomentTest p (momentResidual cavity g ell z)
  let f:=momentLocalChange N d cavity o selector z
  let fgeo:BallLabelledSpace N d→ℂ:=fun ω=>if G ω then f ω else 0
  let C:=sourceMomentLocalChangeCap d B
  let Mp:ℝ:=(sourceMomentResidualCap d)^(2*p-1)
  let m1:=∑g:RegularGraph N d,if Ω g then RegularGraph.weight g*‖momentResidual cavity g ell z‖^(2*p-1) else 0
  have hMp:0≤Mp:=pow_nonneg hM _
  have ht:∀g,A g→‖test g‖≤Mp:=by
    intro g hg
    rw [complexMomentTest_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) ((hsupport z hz hfloor hzB).1 cavity g hg.1) _
  have hgood:∀g,A g→momentAuxiliary N d c g→
      ‖ballLabelledConditionalMean N d o ell fgeo g‖≤C/(N:ℝ)^(9/32:ℝ):=by
    intro g hg hAux
    exact hgeo g o z hz hfloor hzB hg.1 hg.2 hAux.1 hAux.2 cavity
  have hbad:∀g,A g→¬momentAuxiliary N d c g→
      ‖ballLabelledConditionalMean N d o ell fgeo g‖≤C:=by
    intro g hg _
    apply ballLabelledConditionalMean_norm_bound N d o ell fgeo g C hC
    intro labels S
    dsimp only [fgeo]
    by_cases hG:G (canonicalBallLabelledState N d o ell g (labels,S))
    · rw [if_pos hG]
      simp only [f,momentLocalChange,canonicalBallLabelledState_project,canonicalBallLabelledState_permutation_project]
      exact hchange g o z hz hfloor hzB _ hg.1 hg.2 labels S cavity
    · rw [if_neg hG,norm_zero]
      exact hC
  have hgeom:=ball_conditional_test_with_exception N d o ell A (momentAuxiliary N d c) fgeo test
    (C/(N:ℝ)^(9/32:ℝ)) C Mp (by positivity) hC hMp hgood hbad ht
  have hgeomMasked:‖finiteExpectation w (fun ω=>if A (ballLabelledProject ω)∧G ω then
      f ω*test (ballLabelledProject ω) else 0)‖≤
      (C/(N:ℝ)^(9/32:ℝ))*(∑g:RegularGraph N d,if A g then RegularGraph.weight g*‖test g‖ else 0)+
      C*Mp*eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>¬momentAuxiliary N d c g):=by
    convert hgeom using 1
    congr 1
    congr 1
    funext ω
    by_cases ha:A (ballLabelledProject ω) <;>by_cases hg:G ω <;>simp [ha,hg,fgeo]
    all_goals
      apply congrArg (fun t:ℝ=>(C/(N:ℝ)^(9/32:ℝ))*t+
        C*Mp*eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>¬momentAuxiliary N d c g))
      apply Finset.sum_congr rfl
      intro g _
      by_cases hg:A g <;>simp [hg]
  have hlower:(∑g:RegularGraph N d,if A g then RegularGraph.weight g*‖test g‖ else 0) ≤ m1:=by
    apply Finset.sum_le_sum
    intro g _
    have hw:=RegularGraph.weight_nonnegative g
    by_cases hΩ:Ω g
    · by_cases hT:momentTreeEvent N d o c g
      · simp only [A,hΩ,hT,and_self,if_true,test,complexMomentTest_norm,m1]
        exact le_rfl
      · simp only [A,hΩ,hT,and_false,if_false,if_true,test,complexMomentTest_norm]
        positivity
    · simp only [A,hΩ,false_and,if_false]
      exact le_rfl
  have hgeom':‖finiteExpectation w (fun ω=>if A (ballLabelledProject ω)∧G ω then
      f ω*test (ballLabelledProject ω) else 0)‖≤
      (C/(N:ℝ)^(9/32:ℝ))*m1+2*C*Mp/(N:ℝ)^D:=by
    apply hgeomMasked.trans
    have hm:=mul_le_mul_of_nonneg_left hlower (show 0≤C/(N:ℝ)^(9/32:ℝ) by positivity)
    have he:=mul_le_mul_of_nonneg_left haux (mul_nonneg hC hMp)
    exact (add_le_add hm he).trans_eq (by dsimp only [C,Mp];ring)
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hball':4*(d+1)^ell≤N:=(Nat.mul_le_mul_left 4
    (Nat.pow_le_pow_right (by omega:0<d+1) hell)).trans hball
  have hWmass:eventMass w W≤1/(N:ℝ)^D:=by
    change eventMass (ballLabelledWeight N d o ell) (fun ω=>momentWeakFailure N d a c β z
      (ballLabelledProject (ballLabelledPermutation N d selector ω)))≤_
    rw [ball_labelled_resampling_stationary N d o ell selector (by omega) (by omega) hball']
    exact hweak z hz hzB hfloor ⌊(N:ℝ)^c⌋₊
  have hweakTerm:=finiteExpectation_event_product_bound w (ballLabelledWeight_nonnegative N d o ell)
    (fun ω=>A (ballLabelledProject ω)∧¬G ω) W f (fun ω=>test (ballLabelledProject ω)) C Mp hC hMp
    (fun ω hw hg=>(hsupport z hz hfloor hzB).2 cavity o ω hw hg.1.1 hg.1.2)
    (fun ω hg=>ht (ballLabelledProject ω) hg.1)
  have hweak':‖finiteExpectation w (fun ω=>if A (ballLabelledProject ω)∧¬G ω∧W ω then
      f ω*test (ballLabelledProject ω) else 0)‖≤C*Mp/(N:ℝ)^D:=by
    have heq:(fun ω=>if (A (ballLabelledProject ω)∧¬G ω)∧W ω then
        f ω*test (ballLabelledProject ω) else 0)=
        (fun ω=>if A (ballLabelledProject ω)∧¬G ω∧W ω then f ω*test (ballLabelledProject ω) else 0):=by
      funext ω
      simp only [and_assoc]
    rw [heq] at hweakTerm
    exact hweakTerm.trans ((mul_le_mul_of_nonneg_left hWmass (mul_nonneg hC hMp)).trans_eq (by ring))
  have hcover (ω:BallLabelledSpace N d):
      ¬A (ballLabelledProject (ballLabelledPermutation N d selector ω))↔G ω∨W ω:=
    moment_exit_cover N d a c β z o (ballLabelledProject (ballLabelledPermutation N d selector ω))
  have hpartition:=exit_expectation_partition w (fun ω=>A (ballLabelledProject ω))
    (fun ω=>A (ballLabelledProject (ballLabelledPermutation N d selector ω))) G W hcover
    (fun ω=>f ω*test (ballLabelledProject ω))
  rw [hpartition]
  exact ((norm_add_le _ _).trans (add_le_add hgeom' hweak')).trans_eq (by ring)

end SpectralConsequences
