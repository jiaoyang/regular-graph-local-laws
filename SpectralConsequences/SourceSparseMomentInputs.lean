import SpectralConsequences.SourceUniformResidualCaps
import SpectralConsequences.QuadraticDensityAbsorption

/-! The sparse-site error in the genuine source moment identity is quadratic
in the actual nominal error. No sparse averaging certificate is assumed. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceSparseMomentInputsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceSparseMomentCap (d:ℕ)(B:ℝ):ℝ:=
  max (sourceExceptionalCavityCap d B+1) (sourceGreenEntryCap d+5)

namespace RegularGraph

theorem eventually_source_sparse_moment_inputs (a b d:ℕ)(c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)
    (hB:0≤B)(hgap:2*β<1-c):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(z:ℂ),
      0<z.im→‖z‖≤B→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ z→
      let ell:=actualCavityDepth a d N z-1
      let R:=logarithmicRadius (c/4) d N
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      ‖g.Q z-cavityIterate z (g.Q z) (ell+1)-trivialCavityCorrection N d ell z-
        treeRestrictedCavityResidual g R ell z‖≤ε^2 ∧
      ‖empiricalTransform g.H z-regularRootValue d ell (g.Q z) z-trivialTraceCorrection N d ell z-
        treeRestrictedTraceResidual g R ell z‖≤ε^2:=by
  let K:=sourceSparseMomentCap d B
  have hK:0≤K:=by
    have hE:=sourceExceptionalCavityCap_nonnegative d hd B hB
    exact (by linarith:0≤sourceExceptionalCavityCap d B+1).trans (le_max_left _ _)
  filter_upwards [eventually_source_restricted_cavity_error a b d c β B ha hb hd hc hβ hβc hB,
    eventually_source_restricted_trace_error a b d c β B ha hb hd hc hβ hβc hB,
    eventually_trivial_corrections_norm_le_one a b d ha hb hd,
    eventually_source_recursion_smallness a b d β ha hb hd hβ,
    eventually_quadratic_density_absorbed a d 0 0 β (1-c) K hd hβ.le hgap,
    Filter.eventually_ge_atTop 1] with N hQ hT hcorr hsmall hdensity hN
  intro g z hz hzB hfloor hold
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let R:=logarithmicRadius (c/4) d N
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let ρ:=((nonTreeCenters g.graph R).card:ℝ)/(N:ℝ)
  have hρ:0≤ρ:=by dsimp only [ρ];positivity
  have hNp:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  have hbad:((nonTreeCenters g.graph R).card:ℝ)≤(N:ℝ)^c:=
    (Nat.cast_le.mpr hold.1.2).trans (Nat.floor_le (Real.rpow_nonneg hNp.le c))
  have hρK:ρ*K≤K/(N:ℝ)^(1-c):=by
    calc
      _≤((N:ℝ)^c/(N:ℝ))*K:=mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hbad hNp.le) hK
      _=_:=by rw [Real.rpow_sub hNp,Real.rpow_one,div_div_eq_mul_div];ring
  have hρeps:ρ*K≤ε^2:=hρK.trans (by
    simpa only [pow_zero,mul_one,div_one] using hdensity z hz.le)
  have hcq:‖trivialCavityCorrection N d ell z‖≤1:=(hcorr z hz hfloor).1
  have hct:‖trivialTraceCorrection N d ell z‖≤1:=(hcorr z hz hfloor).2
  have hs:((ell:ℝ)+4)*‖g.Q z-semicircleRoot z‖≤1/2:=
    (mul_le_mul_of_nonneg_left hold.2.1 (by positivity)).trans (hsmall z hz hfloor)
  constructor
  · apply (hQ g z _ hz hzB hfloor hold).trans
    apply (mul_le_mul_of_nonneg_left _ hρ).trans hρeps
    exact (add_le_add_left hcq _).trans (le_max_left _ _)
  · apply (hT g z _ hz hzB hfloor hold hs).trans
    apply (mul_le_mul_of_nonneg_left _ hρ).trans hρeps
    exact (add_le_add_left hct _).trans (by
      change sourceGreenEntryCap d+4+1≤K
      simpa only [show (4:ℝ)+1=5 by norm_num,add_assoc] using (le_max_right
        (sourceExceptionalCavityCap d B+1) (sourceGreenEntryCap d+5)))

end RegularGraph
end SpectralConsequences
