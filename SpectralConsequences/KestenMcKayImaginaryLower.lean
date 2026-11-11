import SpectralConsequences.PoissonTraceIntegral

/-! The actual reference imaginary part controls the spectral height on a
bounded domain. This absorbs the additive 1/N switching term into Ward variance. -/
open Set MeasureTheory
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem kestenMcKayStieltjes_im_lower (d:ℕ)(hd:3≤d)(E η B:ℝ)
    (hη:0<η)(hE:|E|≤B)(hηB:η≤B):
    η/(2*(B+2)^2)≤(kestenMcKayStieltjes d ((E:ℂ)+(η:ℂ)*Complex.I)).im:=by
  have hB:0≤B:=hη.le.trans hηB
  have hc:=kestenMcKayDensity_continuousOn d hd
  have hker:Continuous (fun x:ℝ=>η/((x-E)^2+η^2)):=
    continuous_const.div (by fun_prop) (fun x=>ne_of_gt (by positivity))
  have hf:IntervalIntegrable (fun x:ℝ=>kestenMcKayDensity d x*(η/(2*(B+2)^2)))
      volume (-2:ℝ) 2:=(hc.mul continuousOn_const).intervalIntegrable_of_Icc (by norm_num)
  have hg:IntervalIntegrable (fun x:ℝ=>kestenMcKayDensity d x*(η/((x-E)^2+η^2)))
      volume (-2:ℝ) 2:=(hc.mul hker.continuousOn).intervalIntegrable_of_Icc (by norm_num)
  rw [kestenMcKayStieltjes_im_eq_poisson d hd E η hη]
  calc
    _=(∫x in (-2:ℝ)..2,kestenMcKayDensity d x*(η/(2*(B+2)^2))):=by
      rw [intervalIntegral.integral_mul_const,kestenMcKayDensity_integral d hd,one_mul]
    _≤_:=by
      apply intervalIntegral.integral_mono_on (by norm_num) hf hg
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (kestenMcKayDensity_nonnegative d hd x)
      have hx2:|x|≤2:=abs_le.mpr hx
      have hdiff:|x-E|≤B+2:=by
        exact (abs_sub x E).trans (by linarith)
      have hs:(x-E)^2≤(B+2)^2:=by
        have hh:=sq_le_sq₀ (abs_nonneg (x-E)) (by positivity:0≤B+2) |>.mpr hdiff
        simpa only [sq_abs] using hh
      have hηsq:η^2≤B^2:=sq_le_sq₀ hη.le hB |>.mpr hηB
      exact div_le_div_of_nonneg_left hη.le (by positivity) (by nlinarith)

theorem bounded_kestenMcKay_imaginary_lower (d:ℕ)(hd:3≤d)(z:ℂ)(hz:0<z.im)
    (B:ℝ)(hB:‖z‖≤B):
    z.im/(2*(B+2)^2)≤(kestenMcKayTransform d (semicircleRoot z) z).im:=by
  have hh:=kestenMcKayStieltjes_im_lower d hd z.re z.im B hz
    ((Complex.abs_re_le_norm z).trans hB) ((Complex.im_le_norm z).trans hB)
  rw [Complex.re_add_im,kestenMcKayStieltjes_eq_transform d hd z hz] at hh
  exact hh

theorem bounded_height_le_reference_imaginary (d:ℕ)(hd:3≤d)(z:ℂ)(hz:0<z.im)
    (B:ℝ)(hB:‖z‖≤B):
    z.im≤2*(B+2)^2*(kestenMcKayTransform d (semicircleRoot z) z).im:=by
  have hB0:0≤B:=(norm_nonneg z).trans hB
  have hh:=bounded_kestenMcKay_imaginary_lower d hd z hz B hB
  have hmul: z.im≤(kestenMcKayTransform d (semicircleRoot z) z).im*(2*(B+2)^2):=
    (div_le_iff₀ (by positivity)).mp hh
  nlinarith

end SpectralConsequences
