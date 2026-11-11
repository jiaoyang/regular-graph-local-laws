import SpectralConsequences.SourceMomentEvents
import SpectralConsequences.CanonicalBallSupport
import SpectralConsequences.ComplexMomentAlgebra

/-! Actual pointwise local-change and moment-test caps on the nonzero
support of the reversible ball sampling law. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceMomentSupportCapsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceMomentResidualCap (d:ℕ):ℝ:=sourceGreenEntryCap d+11

namespace RegularGraph

theorem eventually_source_moment_support_caps (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32) (hB:0≤B):
    ∀ᶠ N:ℕ in Filter.atTop,∀(z:ℂ),0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→
      let ell:=actualCavityDepth a d N z-1
      let selector:=logarithmicRadius (c/4) d N/4
      (∀(cavity:Bool)(g:LocalLaw.RegularGraph N d),momentSourceEvent N d a c β z g→
        ‖momentResidual cavity g ell z‖≤sourceMomentResidualCap d) ∧
      (∀(cavity:Bool)(o:Fin N)(ω:BallLabelledSpace N d),ballLabelledWeight N d o ell ω≠0→
        momentSourceEvent N d a c β z (ballLabelledProject ω)→momentTreeEvent N d o c (ballLabelledProject ω)→
        ‖momentLocalChange N d cavity o selector z ω‖≤sourceMomentLocalChangeCap d B):=by
  have hC:0≤sourceGreenEntryCap d:=by
    have hh:=finiteReferenceConstant_ge_one d hd
    dsimp only [sourceGreenEntryCap];linarith
  filter_upwards [eventually_source_all_sample_local_change_cap a b d c β B ha hb hd hc hβ hβc hB,
    eventually_source_residual_norm_caps a b d c β B ha hb hd hc hβ hβc hB]
    with N hchange hres
  intro z hz hfloor hzB
  dsimp only
  constructor
  · intro cavity g hold
    have hh:=hres g z ⌊(N:ℝ)^c⌋₊ hz hzB hfloor hold
    cases cavity with
    | false =>
      simp only [momentResidual,Bool.false_eq_true,if_false]
      exact hh.2.trans (by dsimp only [sourceMomentResidualCap];linarith)
    | true =>
      simp only [momentResidual,if_true]
      exact hh.1.trans (by dsimp only [sourceMomentResidualCap];linarith)
  · intro cavity o ω hw hold htree
    obtain ⟨g,data,hω⟩:=canonicalBallLabelledState_support_surjective N d o
      (actualCavityDepth a d N z-1) ω hw
    rcases data with ⟨labels,S⟩
    rw [hω,canonicalBallLabelledState_project] at hold htree
    rw [hω]
    simp only [momentLocalChange,canonicalBallLabelledState_project,canonicalBallLabelledState_permutation_project]
    exact hchange g o z hz hfloor hzB _ hold htree labels S cavity

end RegularGraph
end SpectralConsequences
