import SpectralConsequences.SourceMomentObservables

/-! The literal old recursion targets are bounded under the actual weak prior. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
namespace RegularGraph

theorem eventually_source_moment_target_cap (a b d:ℕ)(β:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hβ:0<β):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→∀R ω bad:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N) R ω bad z→
      ∀cavity:Bool,‖momentRecursionTarget cavity g (actualCavityDepth a d N z-1) z‖≤5:=by
  filter_upwards [eventually_trivial_corrections_norm_le_one a b d ha hb hd,
    eventually_source_recursion_smallness a b d β ha hb hd hβ] with N hcorr hsmall
  intro g z hz hfloor R ω bad hold cavity
  let ell:=actualCavityDepth a d N z-1
  have hcq:‖trivialCavityCorrection N d ell z‖≤1:=(hcorr z hz hfloor).1
  have hct:‖trivialTraceCorrection N d ell z‖≤1:=(hcorr z hz hfloor).2
  have hs:((ell:ℝ)+4)*‖g.Q z-semicircleRoot z‖≤1/2:=
    (mul_le_mul_of_nonneg_left hold.2.1 (by positivity)).trans (hsmall z hz hfloor)
  have hδ:‖g.Q z-semicircleRoot z‖≤1:=by
    have hn:0≤(ell:ℝ):=Nat.cast_nonneg ell
    nlinarith [norm_nonneg (g.Q z-semicircleRoot z)]
  have hsn:((ell+1:ℕ):ℝ)*‖g.Q z-semicircleRoot z‖≤1/2:=by
    push_cast
    nlinarith [norm_nonneg (g.Q z-semicircleRoot z)]
  have hY:=cavity_iterate_norm_le_three (semicircleRoot z) z (g.Q z) (ell+1)
    (semicircleRoot_equation z) (semicircleRoot_norm_le_one z) hsn hδ
  have hX:=regularRootValue_norm_le_four d ell hd (g.Q z) z hz (g.Q_im_nonnegative z hz) hs
  cases cavity with
  | false =>
    simp only [momentRecursionTarget,Bool.false_eq_true,if_false]
    exact (norm_add_le _ _).trans (by linarith)
  | true =>
    simp only [momentRecursionTarget,if_true]
    exact (norm_add_le _ _).trans (by linarith)

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_source_moment_target_cap
