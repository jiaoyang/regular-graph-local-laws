import SpectralConsequences.SourceCavityAllSamplingCap
import SpectralConsequences.SourceTraceAllSamplingCap
import SpectralConsequences.SourceUniformResidualCaps

/-! The two actual local observables used in Proposition7.2. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceMomentObservablesDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def momentLocalObservable {N d:ℕ} (cavity:Bool) (g:RegularGraph N d) (o:Fin N) (z:ℂ):ℂ:=
  if cavity then cavityAtVertex g.graph d z o else g.G z o o

def momentRecursionTarget {N d:ℕ} (cavity:Bool) (g:RegularGraph N d) (ell:ℕ) (z:ℂ):ℂ:=
  if cavity then cavityIterate z (g.Q z) (ell+1)+trivialCavityCorrection N d ell z
  else regularRootValue d ell (g.Q z) z+trivialTraceCorrection N d ell z

def momentResidual {N d:ℕ} (cavity:Bool) (g:RegularGraph N d) (ell:ℕ) (z:ℂ):ℂ:=
  if cavity then g.Q z-cavityIterate z (g.Q z) (ell+1)-trivialCavityCorrection N d ell z
  else empiricalTransform g.H z-regularRootValue d ell (g.Q z) z-trivialTraceCorrection N d ell z

def sourceMomentLocalChangeCap (d:ℕ) (B:ℝ):ℝ:=
  sourceGreenEntryCap d+(sourceGreenEntryCap d)^2*sourceGreenPivotCap d B+
    2*finiteExtraReferenceConstant d+2

namespace RegularGraph

theorem eventually_source_all_sample_local_change_cap (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32) (hB:0≤B):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (S:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))) (cavity:Bool),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let new:=g.labelledResampledGraph T labels S (logarithmicRadius (c/4) d N/4)
      ‖momentLocalObservable cavity g o z-momentLocalObservable cavity new o z‖≤
        sourceMomentLocalChangeCap d B:=by
  have hC:0≤sourceGreenEntryCap d:=by
    have hh:=finiteReferenceConstant_ge_one d hd
    dsimp only [sourceGreenEntryCap];linarith
  have hP:0≤sourceGreenPivotCap d B:=by
    have hh:=finiteReferenceConstant_ge_one d hd
    dsimp only [sourceGreenPivotCap];positivity
  filter_upwards [eventually_source_cavity_all_sampling_cap a b d c β B ha hb hd hc hβ hβc hB,
    eventually_source_trace_all_sampling_cap a b d c β B ha hb hd hc hβ hβc hB,
    LocalLaw.RegularGraph.eventually_sourceOmegaWithRadii_green_caps a b d c β B ha hb hd hc hβ hβc hB]
    with N hcav htrace holdcaps
  intro g o z hz hfloor hzB badCount hold htree ι _ labels S cavity
  dsimp only
  have hcaps:=holdcaps g z badCount hz hzB hfloor hold
  have hnewc:=hcav g o z hz hfloor hzB badCount hold htree labels S
  have hnewt:=(htrace g o z hz hfloor hzB badCount hold htree labels S).2
  have hcv:=g.cavityAtVertex_norm_le_caps (by omega) z hz _ _ hC hP hcaps.1 hcaps.2 o
  cases cavity with
  | false =>
    simp only [momentLocalObservable,Bool.false_eq_true,if_false]
    apply (norm_sub_le _ _).trans
    have hh:=add_le_add (hcaps.1 o o) hnewt
    exact hh.trans (by dsimp only [sourceMomentLocalChangeCap];nlinarith [mul_nonneg (sq_nonneg (sourceGreenEntryCap d)) hP])
  | true =>
    simp only [momentLocalObservable,if_true]
    exact ((norm_sub_le _ _).trans (add_le_add hcv hnewc)).trans
      (by dsimp only [sourceMomentLocalChangeCap];linarith)

end RegularGraph
end SpectralConsequences
