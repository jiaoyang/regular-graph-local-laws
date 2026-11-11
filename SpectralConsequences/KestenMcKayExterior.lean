import SpectralConsequences.PoissonTraceIntegral

/-! An exterior imaginary-part bound from the actual normalized density.
This weaker elementary bound suffices for a positive rigidity exponent. -/
open Set MeasureTheory
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem kestenMcKayStieltjes_im_exterior (d:ℕ)(hd:3≤d)(E η κ:ℝ)
    (hη:0<η)(hκ:0<κ)(hE:2+κ≤|E|):
    (kestenMcKayStieltjes d ((E:ℂ)+(η:ℂ)*Complex.I)).im≤η/κ^2:=by
  have hc:=kestenMcKayDensity_continuousOn d hd
  have hker:Continuous (fun x:ℝ=>η/((x-E)^2+η^2)):=
    continuous_const.div (by fun_prop) (fun x=>ne_of_gt (by positivity))
  have hf:IntervalIntegrable (fun x:ℝ=>kestenMcKayDensity d x*(η/((x-E)^2+η^2)))
      volume (-2:ℝ) 2:=
    (hc.mul hker.continuousOn).intervalIntegrable_of_Icc (by norm_num)
  have hg:IntervalIntegrable (fun x:ℝ=>kestenMcKayDensity d x*(η/κ^2))
      volume (-2:ℝ) 2:=
    (hc.mul continuousOn_const).intervalIntegrable_of_Icc (by norm_num)
  rw [kestenMcKayStieltjes_im_eq_poisson d hd E η hη]
  calc
    _≤∫x in (-2:ℝ)..2,kestenMcKayDensity d x*(η/κ^2):=by
      apply intervalIntegral.integral_mono_on (by norm_num) hf hg
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (kestenMcKayDensity_nonnegative d hd x)
      have hx2:|x|≤2:=abs_le.mpr hx
      have hdiff:κ≤|x-E|:=by
        have hh:|E| - |x|≤|E-x|:=(le_abs_self _).trans (abs_abs_sub_abs_le_abs_sub E x)
        rw [abs_sub_comm E x] at hh
        linarith
      have hsq:κ^2≤(x-E)^2:=by
        have hh:=sq_le_sq₀ hκ.le (abs_nonneg (x-E)) |>.mpr hdiff
        simpa only [sq_abs] using hh
      exact div_le_div_of_nonneg_left hη.le (by positivity) (by nlinarith)
    _=η/κ^2:=by
      rw [intervalIntegral.integral_mul_const,kestenMcKayDensity_integral d hd,one_mul]

end SpectralConsequences
