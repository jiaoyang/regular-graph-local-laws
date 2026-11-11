import SpectralConsequences.SourceMomentSupportCaps
import SpectralConsequences.SourceSparseMomentInputs
import SpectralConsequences.TreeRestrictedSiteMean
import SpectralConsequences.SourceLocalObservableChanges

/-! Actual site-mean, sparse-error and paired increments for both physical
Section 7 residuals. Every assertion concerns the literal ball kernel. -/
open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceMomentSiteInputsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def momentRestrictedResidual {N d:ℕ} (cavity:Bool) (g:RegularGraph N d) (R ell:ℕ) (z:ℂ):ℂ:=
  if cavity then RegularGraph.treeRestrictedCavityResidual g R ell z else RegularGraph.treeRestrictedTraceResidual g R ell z

def momentSparseError {N d:ℕ} (cavity:Bool) (g:RegularGraph N d) (R ell:ℕ) (z:ℂ):ℂ:=
  momentResidual cavity g ell z-momentRestrictedResidual cavity g R ell z

theorem momentResidual_site_mean {N d:ℕ} (cavity:Bool) (g:RegularGraph N d) (R ell:ℕ) (z:ℂ):
    momentResidual cavity g ell z=finiteComplexMean (fun o:Fin N=>
      if (graphBall g.graph o R).IsTree then
        momentLocalObservable cavity g o z-momentRecursionTarget cavity g ell z else 0)+
      momentSparseError cavity g R ell z := by
  have he:momentRestrictedResidual cavity g R ell z=finiteComplexMean (fun o:Fin N=>
      if (graphBall g.graph o R).IsTree then
        momentLocalObservable cavity g o z-momentRecursionTarget cavity g ell z else 0):=by
    cases cavity with
    | false => simpa only [momentRestrictedResidual,momentLocalObservable,momentRecursionTarget,Bool.false_eq_true,if_false] using RegularGraph.treeRestrictedTraceResidual_eq_site_mean g R ell z
    | true => simpa only [momentRestrictedResidual,momentLocalObservable,momentRecursionTarget,if_true] using RegularGraph.treeRestrictedCavityResidual_eq_site_mean g R ell z
  rw [←he]
  unfold momentSparseError
  ring

namespace RegularGraph

theorem eventually_source_moment_site_inputs (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32)
    (hB:0≤B) (hgap:2*β<1-c):
    ∀ᶠ N:ℕ in atTop,∀z:ℂ,0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ‖z‖≤B →
      let ell:=actualCavityDepth a d N z-1
      let R:=logarithmicRadius (c/4) d N
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      let V:=sourceMomentVariance a d N (logarithmicRadius β d N) (sourceWardVarianceConstant d B) z
      (∀(cavity:Bool)(g:LocalLaw.RegularGraph N d),momentSourceEvent N d a c β z g→
        ‖momentSparseError cavity g R ell z‖≤ε^2) ∧
      (∀(cavity:Bool)(o:Fin N)(ω:BallLabelledSpace N d),ballLabelledWeight N d o ell ω≠0→
        momentSourceEvent N d a c β z (ballLabelledProject ω)∧momentTreeEvent N d o c (ballLabelledProject ω)→
        momentSourceEvent N d a c β z (ballLabelledProject (ballLabelledPermutation N d (R/4) ω))∧
          momentTreeEvent N d o c (ballLabelledProject (ballLabelledPermutation N d (R/4) ω))→
        ‖momentLocalChange N d cavity o (R/4) z ω‖≤
          sourceLocalObservableChangeConstant d β B*Real.log (N:ℝ)*ε ∧
        ‖momentResidual cavity (ballLabelledProject ω) ell z-
          momentResidual cavity (ballLabelledProject (ballLabelledPermutation N d (R/4) ω)) ell z‖≤V):=by
  filter_upwards [eventually_source_sparse_moment_inputs a b d c β B ha hb hd hc hβ hβc hB hgap,
    eventually_source_local_observable_changes a b d c β B ha hb hd hc hβ hβc hB,
    eventually_source_ward_variance_bound a b d c β B ha hb hd hc hβ hβc hB]
    with N hsparse hlocal hglobal
  intro z hz hfloor hzB
  dsimp only
  constructor
  · intro cavity g hold
    have hh:=hsparse g z hz hzB hfloor hold
    cases cavity with
    | false => exact hh.2
    | true => exact hh.1
  · intro cavity o ω hw hold hnew
    obtain ⟨g,data,hω⟩:=canonicalBallLabelledState_support_surjective N d o
      (actualCavityDepth a d N z-1) ω hw
    rcases data with ⟨labels,S⟩
    rw [hω,canonicalBallLabelledState_project] at hold
    rw [hω,canonicalBallLabelledState_permutation_project] at hnew
    have hl:=hlocal g o z hz hfloor hzB _ hold.1 hold.2 labels S hnew.1 hnew.2
    have hg:=hglobal g o z hz hfloor hzB _ hold.1 labels S hnew.1
    rw [hω]
    simp only [momentLocalChange,canonicalBallLabelledState_project,canonicalBallLabelledState_permutation_project]
    cases cavity with
    | false => exact ⟨hl.2,hg.2.2.2⟩
    | true => exact ⟨hl.1,hg.2.2.1⟩

end RegularGraph
end SpectralConsequences
