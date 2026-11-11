import SpectralConsequences.CorrectionDepthBounds
import SpectralConsequences.TrivialTraceCap
import SpectralConsequences.SourceRestrictedResidualCaps
import SpectralConsequences.SourceRecursionSmallness
import LocalLaw.OutsideCavityMean

/-! Uniform bounds for the literal corrected residuals on the genuine weak
event. Exceptional-event tests can therefore be bounded with proved constants. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem eventually_trivial_corrections_norm_le_one (a b d:ℕ)(ha:12≤a)(hb:25*a≤b)(hd:3≤d):
    ∀ᶠ N:ℕ in Filter.atTop,∀z:ℂ,0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      let ell:=actualCavityDepth a d N z-1
      ‖trivialCavityCorrection N d ell z‖≤1 ∧‖trivialTraceCorrection N d ell z‖≤1:=by
  filter_upwards [eventually_correction_numerator_height a b d ha hb hd,
    Filter.eventually_ge_atTop 1] with N hbudget hN
  intro z hz hfloor
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let k:ℝ:=((d-1:ℕ):ℝ)
  let C:=uniformCorrectionConstant d
  have hk:1≤k:=by dsimp only [k];exact_mod_cast (show 1≤d-1 by omega)
  have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
  have hCq:8*k≤C:=by dsimp only [C,uniformCorrectionConstant,k];nlinarith
  have hCt:32*((d:ℝ)+1)≤C:=by dsimp only [C,uniformCorrectionConstant];nlinarith
  have hheight:C*k^ell≤(N:ℝ)*z.im:=hbudget z hz hfloor
  have hden:0<(N:ℝ)*z.im:=mul_pos (Nat.cast_pos.mpr (by omega)) hz
  constructor
  · apply (trivialCavityCorrection_norm_le N d ell hN hd z hz).trans
    apply (div_le_one hden).mpr
    calc
      _=(8*k)*k^ell:=by rw [pow_succ];ring
      _≤C*k^ell:=mul_le_mul_of_nonneg_right hCq (by positivity)
      _≤_:=hheight
  · apply (trivialTraceCorrection_norm_le N d ell hN hd z hz).trans
    apply (div_le_one hden).mpr
    exact (mul_le_mul_of_nonneg_right hCt (by positivity)).trans hheight

namespace RegularGraph

theorem eventually_source_residual_norm_caps (a b d:ℕ)(c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hB:0≤B):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(z:ℂ)(badCount:ℕ),
      0<z.im→‖z‖≤B→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      let ell:=actualCavityDepth a d N z-1
      ‖g.Q z-cavityIterate z (g.Q z) (ell+1)-trivialCavityCorrection N d ell z‖≤6 ∧
      ‖empiricalTransform g.H z-regularRootValue d ell (g.Q z) z-trivialTraceCorrection N d ell z‖≤
        sourceGreenEntryCap d+5:=by
  filter_upwards [eventually_trivial_corrections_norm_le_one a b d ha hb hd,
    eventually_source_recursion_smallness a b d β ha hb hd hβ,
    LocalLaw.RegularGraph.eventually_sourceOmegaWithRadii_green_caps a b d c β B ha hb hd hc hβ hβc hB,
    Filter.eventually_ge_atTop 1] with N hcorr hsmall hcap hN
  intro g z badCount hz hzB hfloor hold
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  have hcq:= (hcorr z hz hfloor).1
  have hct:= (hcorr z hz hfloor).2
  have hprior:‖g.Q z-semicircleRoot z‖≤scalarScale (spectralScale z)
      (graphPaperError a d N (logarithmicRadius β d N) z):=hold.2.1
  have hs:((ell:ℝ)+4)*‖g.Q z-semicircleRoot z‖≤1/2:=
    (mul_le_mul_of_nonneg_left hprior (by positivity)).trans (hsmall z hz hfloor)
  have hδ:‖g.Q z-semicircleRoot z‖≤1:=by
    have hn:0≤(ell:ℝ):=Nat.cast_nonneg ell
    nlinarith [norm_nonneg (g.Q z-semicircleRoot z)]
  have hsn:((ell+1:ℕ):ℝ)*‖g.Q z-semicircleRoot z‖≤1/2:=by
    push_cast
    nlinarith [norm_nonneg (g.Q z-semicircleRoot z)]
  have hQ:‖g.Q z‖≤2:=by
    have hh:=norm_add_le (g.Q z-semicircleRoot z) (semicircleRoot z)
    rw [sub_add_cancel] at hh
    exact hh.trans (by have hm:=semicircleRoot_norm_le_one z;linarith)
  have hY:=cavity_iterate_norm_le_three (semicircleRoot z) z (g.Q z) (ell+1)
    (semicircleRoot_equation z) (semicircleRoot_norm_le_one z) hsn hδ
  have hX:=regularRootValue_norm_le_four d ell hd (g.Q z) z hz (g.Q_im_nonnegative z hz) hs
  have htrace:‖empiricalTransform g.H z‖≤sourceGreenEntryCap d:=by
    letI:Nonempty (Fin N):=⟨⟨0,by omega⟩⟩
    have hmean:empiricalTransform g.H z=finiteComplexMean (fun i:Fin N=>g.G z i i):=by
      rw [empiricalTransform_eq_vertex_mean]
      simp only [finiteComplexMean,Fintype.card_fin,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast]
    rw [hmean]
    exact LocalLaw.finiteComplexMean_norm_bound _ _ (fun i=>(hcap g z badCount hz hzB hfloor hold).1 i i)
  constructor
  · exact ((norm_sub_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)).trans (by linarith)
  · exact ((norm_sub_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)).trans (by linarith)

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_source_residual_norm_caps
