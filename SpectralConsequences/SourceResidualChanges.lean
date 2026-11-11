import SpectralConsequences.SourceRecursionSmallness
import SpectralConsequences.TrivialCorrections
import SpectralConsequences.FiniteResolventSpectrum
import LocalLaw.IndependentRadiusEvents
import LocalLaw.EffectiveModelRadius

/-! Actual residual changes under two source weak events. All recursion
smallness is derived uniformly from the actual error/domain parameters. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
namespace RegularGraph

theorem eventually_source_residual_changes (a b d:ℕ)(β:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hβ:0<β):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g h:LocalLaw.RegularGraph N d)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→∀R ω bad bad':ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N) R ω bad z→
      h.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N) R ω bad' z→
      let ell:=actualCavityDepth a d N z-1
      (‖(g.Q z-cavityIterate z (g.Q z) (ell+1)-trivialCavityCorrection N d ell z)-
        (h.Q z-cavityIterate z (h.Q z) (ell+1)-trivialCavityCorrection N d ell z)‖≤5*‖g.Q z-h.Q z‖) ∧
      (‖(empiricalTransform g.H z-regularRootValue d ell (g.Q z) z-trivialTraceCorrection N d ell z)-
        (empiricalTransform h.H z-regularRootValue d ell (h.Q z) z-trivialTraceCorrection N d ell z)‖≤
          ‖empiricalTransform g.H z-empiricalTransform h.H z‖+32*‖g.Q z-h.Q z‖):=by
  filter_upwards [eventually_source_recursion_smallness a b d β ha hb hd hβ]
    with N hsmall
  intro g h z hz hfloor R ω bad bad' hg hh
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  have hs:=hsmall z hz hfloor
  change ((ell:ℝ)+4)*scalarScale (spectralScale z)
    (graphPaperError a d N (logarithmicRadius β d N) z)≤1/2 at hs
  have hgsmall:((ell:ℝ)+4)*‖g.Q z-semicircleRoot z‖≤1/2:=
    (mul_le_mul_of_nonneg_left hg.2.1 (by positivity)).trans hs
  have hhsmall:((ell:ℝ)+4)*‖h.Q z-semicircleRoot z‖≤1/2:=
    (mul_le_mul_of_nonneg_left hh.2.1 (by positivity)).trans hs
  have hgcav:((ell+1:ℕ):ℝ)*‖g.Q z-semicircleRoot z‖≤1/2:=by
    push_cast
    nlinarith [norm_nonneg (g.Q z-semicircleRoot z)]
  have hhcav:((ell+1:ℕ):ℝ)*‖h.Q z-semicircleRoot z‖≤1/2:=by
    push_cast
    nlinarith [norm_nonneg (h.Q z-semicircleRoot z)]
  exact ⟨corrected_cavity_residual_change (semicircleRoot_equation z) (semicircleRoot_norm_le_one z)
      (ell+1) hgcav hhcav (trivialCavityCorrection N d ell z),
    corrected_trace_residual_change d ell hd (g.Q z) (h.Q z) (empiricalTransform g.H z)
      (empiricalTransform h.H z) (trivialTraceCorrection N d ell z) z hz
      (g.Q_im_nonnegative z hz) (h.Q_im_nonnegative z hz) hgsmall hhsmall⟩

end RegularGraph
end SpectralConsequences
