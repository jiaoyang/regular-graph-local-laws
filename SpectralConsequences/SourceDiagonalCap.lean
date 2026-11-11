import LocalLaw.SourceTheorem42
import LocalLaw.PairModelReferenceBounds
import LocalLaw.ParameterSmallness
import LocalLaw.RadiusHierarchy

/-! Actual uniform diagonal Green bounds from the proved source local law. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceDiagonalCapDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceEigenvectorConstant (d:ℕ):ℝ:=
  finiteReferenceConstant d+sourceUniformLawConstant d

theorem sourceEigenvectorConstant_positive (d:ℕ)(hd:3≤d):0<sourceEigenvectorConstant d:=by
  have hF:=finiteReferenceConstant_ge_one d hd
  have hC:=sourceUniformLawConstant_ge_four d
  unfold sourceEigenvectorConstant
  linarith

theorem realSourcePaperError_twelve_eq_graph (d N r:ℕ)(hd:3≤d)(z:ℂ)(hz:0<z.im):
    realSourcePaperError 12 d N r z=graphPaperError 12 d N r z:=by
  rw [realSourcePaperError_eq_graph 12 d N r hd z hz]
  unfold realGraphPaperError graphPaperError paperError paperBaseError baseError
  rw [show (8:ℝ)*12=((8*12:ℕ):ℝ) by norm_num,Real.rpow_natCast]

def SourceLocalLawGood {N d:ℕ}(g:RegularGraph N d)(hd:1≤d)(β:ℝ):Prop:=
  ∀z:ℂ,0<z.im→Real.log (N:ℝ)^300/(N:ℝ)≤z.im→
    RealSourceLocalLawAt hd 12 (logarithmicRadius β d N)
      (sourceUniformLawConstant d) z g

namespace RegularGraph
variable {N d:ℕ}

theorem diagonal_cap_of_source_local_law (g:LocalLaw.RegularGraph N d)(hd:3≤d)
    (r R:ℕ)(hN:1≤N)(hmargin:4*r+1≤R)
    (hballs:∀v,graphBallExcess g.graph v R≤finiteOmega d)(z:ℂ)(hz:0<z.im)
    (hsmall:graphPaperError 12 d N r z≤1)
    (hlaw:RealSourceLocalLawAt (by omega) 12 r (sourceUniformLawConstant d) z g):
    ∀i,‖g.G z i i‖≤sourceEigenvectorConstant d:=by
  have hε:0≤graphPaperError 12 d N r z:=graphPaperError_nonnegative 12 d N r z hN hz.le
  have hC:0≤sourceUniformLawConstant d:=(by norm_num:(0:ℝ)≤4).trans (sourceUniformLawConstant_ge_four d)
  have hscale:scalarScale (spectralScale z) (graphPaperError 12 d N r z)≤1:=
    (scalarScale_le_sqrt (spectralScale_pos hz) hε).trans
      (by simpa only[Real.sqrt_one] using Real.sqrt_le_sqrt hsmall)
  intro i
  have hentry:=hlaw.1 i i
  have hident:(g.pairModel i i r).treeExtensionGreen (by omega) z
      (pairBallLeft g.graph i i r) (pairBallRight g.graph i i r)=g.P r z (semicircleRoot z) i i:=by
    rw[(g.pairModel i i r).treeExtensionGreen_eq_extensionGreen hd z hz]
    exact g.pairModel_P i i r (semicircleRoot z) z
  rw[hident,realSourcePaperError_twelve_eq_graph d N r hd z hz] at hentry
  have herr:‖g.G z i i-g.P r z (semicircleRoot z) i i‖≤sourceUniformLawConstant d:=
    hentry.trans (by simpa only[mul_one] using mul_le_mul_of_nonneg_left hscale hC)
  have htriangle:=norm_sub_le_norm_sub_add_norm_sub (g.G z i i) (g.P r z (semicircleRoot z) i i) 0
  simp only[sub_zero] at htriangle
  exact (htriangle.trans (add_le_add herr (g.pairP_reference_entry_bound hd r R hmargin hballs z hz i i))).trans_eq
    (by unfold sourceEigenvectorConstant;ring)

theorem eventually_source_local_law_diagonal_cap (d:ℕ)(c β:ℝ)
    (hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32):
    ∀ᶠ N:ℕ in Filter.atTop,∀g:LocalLaw.RegularGraph N d,
      LocalLaw.RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g→
      SourceLocalLawGood g (by omega) β→∀z:ℂ,0<z.im→Real.log (N:ℝ)^300/(N:ℝ)≤z.im→
        ∀i,‖g.G z i i‖≤sourceEigenvectorConstant d:=by
  filter_upwards [eventually_paperError_small 12 300 d β (by norm_num) (by norm_num) hd hβ,
    eventually_source_radius_hierarchy 12 d c β hd hc hβ hβc,
    eventually_log_ge_nat 1,Filter.eventually_ge_atTop 1] with N hsmall hradii hlog hN
  intro g hstruct hlaw z hz hfloor
  let r:=logarithmicRadius β d N
  let R:=logarithmicRadius (c/4) d N
  have hmargin:4*r+1≤R:=by
    have h1:=hradii.1
    have h2:=hradii.2.1
    dsimp only[r,R]
    omega
  have hpow:1≤Real.log (N:ℝ)^(4*12):=one_le_pow₀ hlog
  have hinv:(Real.log (N:ℝ)^(4*12))⁻¹≤1:=by
    simpa only[one_div,inv_one] using one_div_le_one_div_of_le (by norm_num:(0:ℝ)<1) hpow
  have herror:graphPaperError 12 d N r z≤1:=(hsmall z hz hfloor).trans hinv
  exact diagonal_cap_of_source_local_law g hd r R hN hmargin hstruct.1 z hz herror (hlaw z hz hfloor)

end RegularGraph
end SpectralConsequences
