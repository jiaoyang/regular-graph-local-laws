import SpectralConsequences.TreeRestrictedResiduals
import SpectralConsequences.RegularRootTaylor
import LocalLaw.IndependentRadiusSourceCaps

/-! Cutoff removal with genuine old-source Green and exceptional-cavity caps. -/
noncomputable section
set_option maxHeartbeats 1400000
namespace SpectralConsequences
open LocalLaw
local instance sourceRestrictedResidualCapsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem regularRootValue_norm_le_four (d ell:ℕ)(hd:3≤d)(q z:ℂ)(hz:0<z.im)(hq:0≤q.im)
    (hsmall:((ell:ℝ)+4)*‖q-semicircleRoot z‖≤1/2):
    ‖regularRootValue d ell q z‖≤4:=by
  let δ:=q-semicircleRoot z
  let md:=kestenMcKayTransform d (semicircleRoot z) z
  let A:=regularRootLinearCoefficient d ell (semicircleRoot z) md
  have hδ:0≤‖δ‖:=norm_nonneg _
  have hn:0≤(ell:ℝ):=Nat.cast_nonneg _
  have hδ8:8*‖δ‖≤1:=by change ((ell:ℝ)+4)*‖δ‖≤1/2 at hsmall;nlinarith
  have hrem:=regularRootValue_taylor_bound d ell hd q z hz hq hsmall
  have hrem1:‖regularRootValue d ell q z-md-A*δ‖≤1:=by
    apply hrem.trans
    have hh:=mul_le_mul_of_nonneg_right hsmall hδ
    change ((ell:ℝ)+4)*‖δ‖*‖δ‖≤(1/2)*‖δ‖ at hh
    nlinarith
  have hAm:‖A*δ‖≤1:=by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (regularRootLinearCoefficient_norm_le_eight d ell hd z hz) hδ).trans hδ8
  have heq:regularRootValue d ell q z=(regularRootValue d ell q z-md-A*δ)+md+A*δ:=by ring
  rw [heq]
  exact ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)).trans
    (by have hmd:=kestenMcKayTransform_norm_le_two d hd z hz;change ‖_‖+‖md‖+‖A*δ‖≤4;linarith)

namespace RegularGraph

theorem eventually_source_restricted_cavity_error (a b d:ℕ)(c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hB:0≤B):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(z:ℂ)(badCount:ℕ),
      0<z.im→‖z‖≤B→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      let ell:=actualCavityDepth a d N z-1
      let R:=logarithmicRadius (c/4) d N
      ‖g.Q z-cavityIterate z (g.Q z) (ell+1)-trivialCavityCorrection N d ell z-
        treeRestrictedCavityResidual g R ell z‖≤
        ((nonTreeCenters g.graph R).card:ℝ)/(N:ℝ)*
          (sourceExceptionalCavityCap d B+‖trivialCavityCorrection N d ell z‖):=by
  filter_upwards [LocalLaw.RegularGraph.eventually_sourceOmegaWithRadii_exceptional_cavity_cap
    a b d c β B ha hb hd hc hβ hβc hB,Filter.eventually_ge_atTop 1]
    with N hcap hN
  intro g z badCount hz hzB hfloor hold
  dsimp only
  have hn:baselineCavityDepth a d N≤actualCavityDepth a d N z:=
    (nonresonantDepth_bounds _ _).1
  have hb0:2≤baselineCavityDepth a d N:=by unfold baselineCavityDepth;omega
  have hell:actualCavityDepth a d N z-1+1=actualCavityDepth a d N z:=by omega
  apply treeRestrictedCavityResidual_error g (by omega)
    (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) z _
    (add_nonneg (sourceExceptionalCavityCap_nonnegative d hd B hB) (norm_nonneg _))
  intro o _
  apply (norm_sub_le _ _).trans
  apply add_le_add_right _
  simpa only [hell] using hcap g z badCount hz hzB hfloor hold o

theorem eventually_source_restricted_trace_error (a b d:ℕ)(c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hB:0≤B):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(z:ℂ)(badCount:ℕ),
      0<z.im→‖z‖≤B→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      let ell:=actualCavityDepth a d N z-1
      let R:=logarithmicRadius (c/4) d N
      ((ell:ℝ)+4)*‖g.Q z-semicircleRoot z‖≤1/2→
      ‖empiricalTransform g.H z-regularRootValue d ell (g.Q z) z-trivialTraceCorrection N d ell z-
        treeRestrictedTraceResidual g R ell z‖≤
        ((nonTreeCenters g.graph R).card:ℝ)/(N:ℝ)*
          (sourceGreenEntryCap d+4+‖trivialTraceCorrection N d ell z‖):=by
  filter_upwards [LocalLaw.RegularGraph.eventually_sourceOmegaWithRadii_green_caps
    a b d c β B ha hb hd hc hβ hβc hB,Filter.eventually_ge_atTop 1]
    with N hcap hN
  intro g z badCount hz hzB hfloor hold
  dsimp only
  intro hsmall
  have hC:0≤sourceGreenEntryCap d:=by
    have hh:=finiteReferenceConstant_ge_one d hd
    unfold sourceGreenEntryCap
    linarith
  apply treeRestrictedTraceResidual_error g (by omega)
    (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) z _ (by positivity)
  intro o _
  have hx:=regularRootValue_norm_le_four d (actualCavityDepth a d N z-1) hd (g.Q z) z hz
    (g.Q_im_nonnegative z hz) hsmall
  have hg:‖g.G z o o‖≤sourceGreenEntryCap d:=(hcap g z badCount hz hzB hfloor hold).1 o o
  exact ((norm_sub_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)).trans
    (by linarith)

end RegularGraph
end SpectralConsequences
