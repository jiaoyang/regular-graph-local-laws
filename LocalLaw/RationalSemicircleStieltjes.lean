import LocalLaw.PhysicalRootStieltjes

/-! # Rational reweighting of the semicircle density

Partial fractions evaluate the genuine density integral with the quadratic
weight c/(a^2-x^2), where a lies strictly outside the support. This is the
Kesten--McKay Stieltjes calculation before specializing its real constants.
-/

open Set Complex MeasureTheory
open scoped Real Interval Topology
noncomputable section
namespace LocalLaw

theorem exterior_semicircle_denominator (a : ℝ) (ha : 2<a) :
    (∀x∈Icc (-2:ℝ) 2,(x:ℂ)-(a:ℂ)≠0) ∧
    (∀x∈Icc (-2:ℝ) 2,(x:ℂ)-(-a:ℂ)≠0) := by
  constructor
  · intro x hx
    apply sub_ne_zero.mpr
    exact Complex.ofReal_injective.ne (ne_of_lt (hx.2.trans_lt ha))
  · intro x hx
    apply sub_ne_zero.mpr
    rw [←Complex.ofReal_neg]
    exact Complex.ofReal_injective.ne (ne_of_gt (by linarith [hx.1]))

theorem rational_semicircle_density_interval_integral (a w c : ℝ) (ha : 2<a)
    (hw : 0<w) (hw1 : w<1) (heq : w^2-a*w+1=0) (z : ℂ) (hz : 0<z.im) :
    (∫x in (-2:ℝ)..2,((c*semicircleDensity x/(a^2-x^2):ℝ):ℂ)/((x:ℂ)-z))=
      (c:ℂ)/((a:ℂ)^2-z^2)*(semicircleRoot z+z*(w:ℂ)/(a:ℂ)) := by
  have hden := exterior_semicircle_denominator a ha
  have hmNorm : ‖(w:ℂ)‖<1 := by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hw] using hw1
  have hmNormNeg : ‖(-w:ℂ)‖<1 := by simpa only [norm_neg] using hmNorm
  have hEqCast : (w:ℂ)^2-(a:ℂ)*(w:ℂ)+1=0 := by exact_mod_cast heq
  have hEqPlus : (-w:ℂ)^2+(a:ℂ)*(-w)+1=0 := by linear_combination hEqCast
  have hEqMinus : (w:ℂ)^2+(-a:ℂ)*(w:ℂ)+1=0 := by linear_combination hEqCast
  have hplus := physical_root_density_interval_integral (-w:ℂ) (a:ℂ) hEqPlus hmNormNeg hden.1
  have hminus := physical_root_density_interval_integral (w:ℂ) (-a:ℂ) hEqMinus hmNorm hden.2
  have hAcont : ContinuousOn (fun x : ℝ => (semicircleDensity x:ℂ)/((x:ℂ)-(a:ℂ))) (Icc (-2:ℝ) 2) :=
    (Complex.continuous_ofReal.comp semicircleDensity_continuous).continuousOn.div
      (by fun_prop : Continuous (fun x : ℝ => (x:ℂ)-(a:ℂ))).continuousOn hden.1
  have hNAcont : ContinuousOn (fun x : ℝ => (semicircleDensity x:ℂ)/((x:ℂ)-(-a:ℂ))) (Icc (-2:ℝ) 2) :=
    (Complex.continuous_ofReal.comp semicircleDensity_continuous).continuousOn.div
      (by fun_prop : Continuous (fun x : ℝ => (x:ℂ)-(-a:ℂ))).continuousOn hden.2
  have hAi := hAcont.intervalIntegrable_of_Icc (μ:=volume) (by norm_num : (-2:ℝ)≤2)
  have hNAi := hNAcont.intervalIntegrable_of_Icc (μ:=volume) (by norm_num : (-2:ℝ)≤2)
  have hZi := (semicircle_kernel_continuous z hz).intervalIntegrable (μ:=volume) (-2:ℝ) 2
  have ha0 : (a:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hAz := real_sub_upperHalfPlane_ne_zero a hz
  have hApz : (a:ℂ)+z≠0 := by
    intro h
    apply real_sub_upperHalfPlane_ne_zero (-a) hz
    simp only [Complex.ofReal_neg]
    linear_combination -h
  have hZden : (a:ℂ)^2-z^2≠0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hApz hAz
  have hpoint : EqOn
      (fun x : ℝ => ((c*semicircleDensity x/(a^2-x^2):ℝ):ℂ)/((x:ℂ)-z))
      (fun x : ℝ => (c:ℂ)/((a:ℂ)^2-z^2)*
        ((semicircleDensity x:ℂ)/((x:ℂ)-z)-
          (((a:ℂ)+z)/(2*(a:ℂ)))*((semicircleDensity x:ℂ)/((x:ℂ)-(a:ℂ)))+
          ((z-(a:ℂ))/(2*(a:ℂ)))*((semicircleDensity x:ℂ)/((x:ℂ)-(-a:ℂ)))))
      (uIcc (-2:ℝ) 2) := by
    intro x hx
    have hx' : x∈Icc (-2:ℝ) 2 := by simpa only [uIcc_of_le (by norm_num : (-2:ℝ)≤2)] using hx
    have hxZ := real_sub_upperHalfPlane_ne_zero x hz
    have hxA := hden.1 x hx'
    have hxNA := hden.2 x hx'
    have hxNA' : (x:ℂ)+(a:ℂ)≠0 := by simpa only [sub_neg_eq_add] using hxNA
    have hApx : (a:ℂ)+(x:ℂ)≠0 := by simpa only [add_comm] using hxNA'
    have hAx : (a:ℂ)-(x:ℂ)≠0 := (sub_ne_zero.mpr (sub_ne_zero.mp hxA).symm)
    have hXden : (a:ℂ)^2-(x:ℂ)^2≠0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero (by simpa only [add_comm] using hxNA') hAx
    push_cast
    simp only [sub_neg_eq_add,sq_sub_sq]
    field_simp (maxDischargeDepth:=20) [hxZ,hxA,hxNA',hApx,hAx,hAz,hApz,ha0]
    ring
  rw [intervalIntegral.integral_congr hpoint,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hZi.sub (hAi.const_mul _)) (hNAi.const_mul _),
    intervalIntegral.integral_sub hZi (hAi.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    semicircle_density_interval_integral z hz,hplus,hminus]
  congr 1
  field_simp [ha0]
  ring

end LocalLaw
