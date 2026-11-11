import LocalLaw.SourceFormalKernelBounds

/-! # Actual inverse-q bounds on bounded spectral domains -/
open Filter
noncomputable section
namespace LocalLaw

theorem eventually_source_formal_kernel_inverse_bound (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in atTop,∀ z q : ℂ,0<z.im → ‖z‖≤B →
      Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      1/(2*(B+1))≤‖q‖ ∧ ‖q⁻¹‖≤2*(B+1) := by
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_log_ge_nat (2*(|B|+1))] with N hnum hLB
  intro z q hz hzB hfloor hprior
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let δ:=‖q-semicircleRoot z‖
  have num:=hnum z hz hfloor
  have hL : 1≤L := num.log_one
  have hB : 0≤B := (norm_nonneg z).trans hzB
  have hδ : 0≤δ := norm_nonneg _
  have hprior' := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative hC1)
  have hscaled := weak_prior_scaled_norm z q hz (C1^2*ε) L
    (mul_nonneg (sq_nonneg C1) num.error_nonnegative) num.error_scaled hprior'
  have hδB : δ*(B+1)≤1/2 := by
    have hBL : 2*(B+1)≤L := (by linarith [le_abs_self B] : 2*(B+1)≤2*(|B|+1)).trans hLB
    have hh:=mul_le_mul_of_nonneg_left (show 2*(B+1)≤L^2 by nlinarith only [hBL,hL]) hδ
    nlinarith only [hh,hscaled]
  have hlo:=cavity_root_norm_lower_bound (semicircleRoot_equation z) (semicircleRoot_norm_le_one z) hzB
  have hmprod : 1≤‖semicircleRoot z‖*(B+1) := (div_le_iff₀ (by linarith : 0<B+1)).mp hlo
  have htri : ‖semicircleRoot z‖≤δ+‖q‖ := by
    have h:=norm_add_le (semicircleRoot z-q) q
    rw [sub_add_cancel,norm_sub_rev] at h
    exact h
  have htriB:=mul_le_mul_of_nonneg_right htri (by linarith : 0≤B+1)
  have hqprod : 1/2≤‖q‖*(B+1) := by nlinarith only [hmprod,htriB,hδB]
  have hqpos : 0<‖q‖ := by nlinarith [norm_nonneg q]
  constructor
  · apply (div_le_iff₀ (by linarith : 0<2*(B+1))).mpr
    nlinarith only [hqprod]
  · rw [norm_inv,←one_div]
    apply (div_le_iff₀ hqpos).mpr
    nlinarith only [hqprod]

namespace RegularGraph
theorem eventually_source_Q_inverse_bound (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ)(rModel R ell ω Cq badCount:ℕ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      g.SourceOmegaPlusWithRadii a rModel (logarithmicRadius β d N) R ell ω Cq badCount C1 o z →
      1/(2*(B+1))≤‖g.Q z‖ ∧ ‖(g.Q z)⁻¹‖≤2*(B+1) := by
  filter_upwards [eventually_source_formal_kernel_inverse_bound a b d c β B C1 ha hb hd hc hβ hβc hC1]
    with N hN
  intro g o z rModel R ell ω Cq badCount hz hzB hfloor hplus
  exact hN z (g.Q z) hz hzB hfloor hplus.cavity
end RegularGraph
end LocalLaw
