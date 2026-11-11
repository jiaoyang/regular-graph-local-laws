import SpectralConsequences.SupportedReversibleMoment
import SpectralConsequences.SourceMomentSiteInputs
import SpectralConsequences.SourceMomentDriftIntegral
import SpectralConsequences.SourceMomentExitIntegral

/-! The genuine source recurrence for both Section7 observables. All local,
global, sparse, conditional-drift and exit quantities are literal proved
objects of the actual uniform regular-graph resampling law. -/
open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2600000
namespace SpectralConsequences
open LocalLaw
local instance sourceMomentRecurrenceDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceMomentLower (N d a:ℕ)(c β:ℝ)(cavity:Bool)(ell:ℕ)(z:ℂ)(n:ℕ):ℝ:=
  ∑g:LocalLaw.RegularGraph N d,if momentSourceEvent N d a c β z g then
    LocalLaw.RegularGraph.weight g*‖momentResidual cavity g ell z‖^n else 0

def sourceMomentExceptionConstant (d p:ℕ)(B:ℝ):ℝ:=
  (sourceMomentDriftCap d+3*sourceMomentLocalChangeCap d B)*(sourceMomentResidualCap d)^(2*p-1)

theorem eventually_source_moment_recurrence (a b d p D:ℕ)(c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hp:1≤p)(hc:0<c)(hc1:c≤1/16)
    (hβ:0<β)(hβc:β≤c/32)(hB:2*(d:ℝ)≤B):
    ∀ᶠ N:ℕ in atTop,∀z:ℂ,0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀cavity:Bool,
      let ell:=actualCavityDepth a d N z-1
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      let L:=Real.log (N:ℝ)
      let V:=sourceMomentVariance a d N (logarithmicRadius β d N) (sourceWardVarianceConstant d B) z
      let A:=sourceTraceDriftConstant d β B*L^(6*a+7)*ε^2+
        sourceMomentLocalChangeCap d B/(N:ℝ)^(9/32:ℝ)+ε^2
      let U:=sourceLocalObservableChangeConstant d β B*L*ε
      truncatedMoment (RegularGraph.weight (N:=N) (d:=d)) (momentSourceEvent N d a c β z)
        (fun g=>momentResidual cavity g ell z) p≤
      A*sourceMomentLower N d a c β cavity ell z (2*p-1)+
      momentIncrementCoefficient p*U*V*sourceMomentLower N d a c β cavity ell z (2*p-2)+
      momentIncrementCoefficient p*U*V^(2*p-1)+sourceMomentExceptionConstant d p B/(N:ℝ)^D:=by
  have hB0:0≤B:=by have hh:=(Nat.cast_le (α:=ℝ)).mpr hd;linarith
  have hgap:2*β<1-c:=by linarith
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [RegularGraph.eventually_source_moment_site_inputs a b d c β B ha hb hd hc hβ hβc hB0 hgap,
    RegularGraph.eventually_source_moment_drift_integral a b d p D c β B ha hb hd hc hc1 hβ hβc hB0,
    eventually_source_moment_exit_integral a b d D c β B ha hb hd hc hc1 hβ hβc hB,
    eventually_source_moment_variance_small a b d β (sourceWardVarianceConstant d B) ha hb hd hβ
      (sourceWardVarianceConstant_nonnegative d B hd hB0),
    eventually_resampling_ball_budget a d hd,hdepth,eventually_log_ge_nat 1,eventually_ge_atTop 1]
    with N hsite hdrift hexit hvar hball hdepth hlog hN
  intro z hz hzB hfloor cavity
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let R:=logarithmicRadius (c/4) d N
  let Ω:=momentSourceEvent N d a c β z
  let χ:=fun o:Fin N=>momentTreeEvent N d o c
  let h:=fun o:Fin N=>fun g:RegularGraph N d=>momentLocalObservable cavity g o z
  let target:=fun g:RegularGraph N d=>momentRecursionTarget cavity g ell z
  let F:=fun g:RegularGraph N d=>momentResidual cavity g ell z
  let error:=fun g:RegularGraph N d=>momentSparseError cavity g R ell z
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let V:=sourceMomentVariance a d N (logarithmicRadius β d N) (sourceWardVarianceConstant d B) z
  let U:=sourceLocalObservableChangeConstant d β B*L*ε
  have hε:0≤ε:=graphPaperError_nonnegative _ _ _ _ _ hN hz.le
  have hU:0≤U:=by
    dsimp only [U,sourceLocalObservableChangeConstant,oldTreeRootErrorConstant,oldTreeFormalConstant]
    positivity
  have hV:0≤V:=(hvar z hz hfloor).1.1
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepth).2
  have hball':4*(d+1)^ell≤N:=(Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by omega) hell)).trans hball
  let E:Fin N→ReversibleExtension (RegularGraph N d) (RegularGraph.weight (N:=N) (d:=d)):=
    fun o=>ballLabelledReversibleExtension N d o ell (R/4) (by omega) (by omega) hball'
  letI:Nonempty (Fin N):=⟨⟨0,by omega⟩⟩
  have hmass:(∑g:RegularGraph N d,RegularGraph.weight g)≤1:=by
    by_cases hne:Nonempty (RegularGraph N d)
    · letI:=hne;rw [RegularGraph.weight_normalized]
    · letI:IsEmpty (RegularGraph N d):=not_nonempty_iff.mp hne
      simp
  have hsite':=hsite z hz hfloor hzB
  have hh:=global_reversible_moment_recurrence_on_support
    (RegularGraph.weight (N:=N) (d:=d)) RegularGraph.weight_nonnegative hmass E Ω χ h target F error p hp
    (sourceTraceDriftConstant d β B*L^(6*a+7)*ε^2)
    (sourceMomentLocalChangeCap d B/(N:ℝ)^(9/32:ℝ)) (ε^2) U V
    (sourceMomentDriftCap d*(sourceMomentResidualCap d)^(2*p-1)/(N:ℝ)^D)
    (3*sourceMomentLocalChangeCap d B*(sourceMomentResidualCap d)^(2*p-1)/(N:ℝ)^D) hU hV
    (fun g _=>momentResidual_site_mean cavity g R ell z)
    (fun g hg=>hsite'.1 cavity g hg)
    (fun o ω hw hold hnew=>(hsite'.2 cavity o ω hw hold hnew).1)
    (fun o ω hw hold hnew=>(hsite'.2 cavity o ω hw hold hnew).2)
    (fun o=>hdrift z hz hfloor hzB cavity o)
    (fun o=>hexit z hz hfloor hzB cavity p o)
  apply hh.trans_eq
  dsimp only [sourceMomentLower,sourceMomentExceptionConstant,Ω,F,U,V,L,ε]
  ring

end SpectralConsequences
