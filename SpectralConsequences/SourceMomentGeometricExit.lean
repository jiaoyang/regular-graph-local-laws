import SpectralConsequences.SourceMomentObservables
import SpectralConsequences.SourceGeometricSwitchExit
import SpectralConsequences.BallConditionalMaskBounds

/-! # The actual geometric exit contribution in the moment identity -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceMomentGeometricExitDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def momentLocalChange (N d:ℕ) (cavity:Bool) (o:Fin N) (selector:ℕ) (z:ℂ)
    (ω:BallLabelledSpace N d):ℂ:=
  momentLocalObservable cavity (ballLabelledProject ω) o z-
    momentLocalObservable cavity (ballLabelledProject (ballLabelledPermutation N d selector ω)) o z

def momentGeometricExit (N d:ℕ) (o:Fin N) (selector R bad:ℕ)
    (ω:BallLabelledSpace N d):Prop:=
  ¬RegularGraph.structural R (finiteOmega d) bad
    (ballLabelledProject (ballLabelledPermutation N d selector ω)) ∨
  ¬(graphBall (ballLabelledProject (ballLabelledPermutation N d selector ω)).graph o R).IsTree

namespace RegularGraph

theorem eventually_source_moment_geometric_exit (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hc1:c≤1/16)
    (hβ:0<β) (hβc:β≤c/32) (hB:0≤B):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ z→
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree→
      LargeTreeCountAux (4*c) (7*c) g→WorkTreeCountAux (4*c) (7*c/8) g→
      let ell:=actualCavityDepth a d N z-1
      let R:=logarithmicRadius (c/4) d N
      ∀cavity:Bool,‖ballLabelledConditionalMean N d o ell (fun ω=>
        if momentGeometricExit N d o (R/4) R ⌊(N:ℝ)^c⌋₊ ω then
          momentLocalChange N d cavity o (R/4) z ω else 0) g‖≤
        sourceMomentLocalChangeCap d B/(N:ℝ)^(9/32:ℝ):=by
  have hC:0≤sourceMomentLocalChangeCap d B:=by
    have hCb:=finiteReferenceConstant_ge_one d hd
    have hCe:=finiteExtraReferenceConstant_ge_one d hd
    dsimp only [sourceMomentLocalChangeCap,sourceGreenEntryCap,sourceGreenPivotCap]
    positivity
  filter_upwards [eventually_source_all_sample_local_change_cap a b d c β B ha hb hd hc hβ hβc hB,
    eventually_source_geometric_switch_exit_concrete a d (finiteOmega d) (4*c)
      (by omega) hd (by linarith) (by linarith)] with N hchange hprob
  intro g o z hz hfloor hzB hold htree hLarge hWork
  dsimp only
  intro cavity
  let ell:=actualCavityDepth a d N z-1
  let R:=logarithmicRadius (c/4) d N
  let selector:=R/4
  have hp:0≤1/(N:ℝ)^(9/32:ℝ):=by positivity
  have hh:=ballLabelledConditionalMean_mask_bound N d o ell
    (momentGeometricExit N d o selector R ⌊(N:ℝ)^c⌋₊)
    (momentLocalChange N d cavity o selector z) g (sourceMomentLocalChangeCap d B)
    (1/(N:ℝ)^(9/32:ℝ)) hC hp ?_ ?_
  · exact hh.trans_eq (by ring)
  · intro labels S _
    simp only [momentLocalChange,canonicalBallLabelledState_project,canonicalBallLabelledState_permutation_project]
    exact hchange g o z hz hfloor hzB _ hold htree labels S cavity
  · intro labels
    have hg:=hprob g o z
    rw [show (4*c)/16=c/4 by ring,show 7*(4*c)/4=7*c by ring,
      show 7*(4*c)/32=7*c/8 by ring,show (4*c)/4=c by ring] at hg
    have hraw:=hg hLarge hWork hold.1.1 htree labels
    simpa only [momentGeometricExit,canonicalBallLabelledState_permutation_project] using hraw

end RegularGraph
end SpectralConsequences
