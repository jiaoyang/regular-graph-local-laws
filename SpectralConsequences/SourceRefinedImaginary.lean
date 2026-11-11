import LocalLaw.IndependentRadiusSourceCaps
import LocalLaw.PairModelReferenceBounds

/-! Refined actual diagonal imaginary-part control on the weak source event. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceRefinedImaginaryDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceRefinedImaginaryCap {N:ℕ} (a d r:ℕ) (z:ℂ):ℝ:=
  finiteReferenceConstant d*(graphKestenMcKayReference d z).im+graphPaperError a d N r z+
    pairSensitivityConstant d*scalarScale (spectralScale z) (graphPaperError a d N r z)

namespace RegularGraph

theorem eventually_source_refined_imaginary (a b d:ℕ) (c β:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(z:ℂ)(badCount:ℕ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      ∀v,(g.G z v v).im≤sourceRefinedImaginaryCap (N:=N) a d (logarithmicRadius β d N) z:=by
  let C:=finiteReferenceConstant d
  let K:=pairSensitivityConstant d
  have hC:0≤C:=(by norm_num:(0:ℝ)≤1).trans (finiteReferenceConstant_ge_one d hd)
  have hCo:=coreConvolutionConstant_nonnegative (finiteOmega d)
  filter_upwards [eventually_source_kernel_feedback a b d β 1 (2*C)
      (coreConvolutionConstant (finiteOmega d)) ha hb hd hβ (by norm_num) (by positivity) hCo,
    eventually_source_radius_hierarchy a d c β hd hc hβ hβc] with N hfeedback hrad
  intro g z badCount hz hfloor hold v
  let r:=effectiveModelRadius a d N β
  let R:=logarithmicRadius (c/4) d N
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let Ψ:=scalarScale (spectralScale z) ε
  have hprior:‖g.Q z-semicircleRoot z‖≤Ψ:=hold.2.1
  have hmarg:4*r+1≤R:=by
    have hr:r≤logarithmicRadius β d N:=Nat.sub_le _ _
    dsimp only [R]
    omega
  have hs:‖g.Q z-semicircleRoot z‖*C*coreConvolutionConstant (finiteOmega d)*(4*(r:ℝ)+2)≤1/2:=by
    have hh:=hfeedback z (g.Q z) hz hfloor (by simpa only [one_mul] using hprior)
    have hr:(r:ℝ)≤(logarithmicRadius β d N:ℝ):=Nat.cast_le.mpr (Nat.sub_le _ _)
    have hfac:0≤‖g.Q z-semicircleRoot z‖*C*coreConvolutionConstant (finiteOmega d):=by positivity
    calc
      _≤‖g.Q z-semicircleRoot z‖*C*coreConvolutionConstant (finiteOmega d)*
        (2*((logarithmicRadius β d N:ℝ)*2+1)):=mul_le_mul_of_nonneg_left (by nlinarith) hfac
      _≤1/2:=by convert hh using 1;ring
  have hp:=g.pairP_reference_im_bound hd r R hmarg hold.1.1 z hz v v
  have hc':=g.pairP_boundary_uniform_stability hd r R hmarg hold.1.1 z (g.Q z) hz
    (g.Q_im_nonnegative z hz) hs v v
  have hg:‖g.G z v v-g.P r z (g.Q z) v v‖≤ε:=hold.2.2 v v
  have hdiff:‖g.G z v v-g.P r z (semicircleRoot z) v v‖≤ε+K*Ψ:=by
    apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    apply add_le_add hg
    exact hc'.trans (mul_le_mul_of_nonneg_left hprior (pairSensitivityConstant_nonnegative d))
  have himnorm:|(g.G z v v).im-(g.P r z (semicircleRoot z) v v).im|≤
      ‖g.G z v v-g.P r z (semicircleRoot z) v v‖:=by
    simpa only [Complex.sub_im] using (Complex.abs_im_le_norm
      (g.G z v v-g.P r z (semicircleRoot z) v v))
  have him:(g.G z v v).im-(g.P r z (semicircleRoot z) v v).im≤ε+K*Ψ:=
    ((le_abs_self _).trans himnorm).trans hdiff
  have him':(g.P r z (semicircleRoot z) v v).im≤C*(graphKestenMcKayReference d z).im:=
    (le_abs_self _).trans hp
  change (g.G z v v).im≤C*(graphKestenMcKayReference d z).im+ε+K*Ψ
  linarith

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_source_refined_imaginary
