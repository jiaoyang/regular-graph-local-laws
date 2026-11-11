import LocalLaw.SemicircleCauchyCircle

/-! # Angular evaluation of the semicircle Stieltjes kernel -/

open Set Complex MeasureTheory
open scoped Real Interval Topology
noncomputable section
namespace LocalLaw

theorem real_sub_upperHalfPlane_ne_zero (x : ℝ) {z : ℂ} (hz : 0<z.im) : (x:ℂ)-z≠0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im,Complex.ofReal_im,Complex.zero_im,zero_sub] at hi
  linarith

theorem semicircle_angular_denominator_continuous (z : ℂ) (hz : 0<z.im) :
    Continuous (fun t : ℝ => ((2*Real.cos t:ℝ):ℂ)-z) ∧
    ∀t : ℝ, ((2*Real.cos t:ℝ):ℂ)-z≠0 := by
  exact ⟨by fun_prop,fun t => real_sub_upperHalfPlane_ne_zero _ hz⟩

theorem unit_circle_polynomial_identity (z : ℂ) (t : ℝ) :
    (circleMap 0 1 t)^2-z*circleMap 0 1 t+1=
      circleMap 0 1 t*(((2*Real.cos t:ℝ):ℂ)-z) := by
  have htrig : (Real.cos t:ℂ)^2+(Real.sin t:ℂ)^2=1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq t
  simp only [circleMap,Complex.ofReal_one,one_mul,zero_add,Complex.exp_mul_I,
    ←Complex.ofReal_cos,←Complex.ofReal_sin,Complex.ofReal_mul,Complex.ofReal_ofNat]
  linear_combination -htrig+(Real.sin t:ℂ)^2*Complex.I_sq

theorem unit_circle_cauchy_integrand (z : ℂ) (_hz : 0<z.im) (t : ℝ) :
    deriv (circleMap 0 1) t •
      ((1-(circleMap 0 1 t)^2)/((circleMap 0 1 t)^2-z*circleMap 0 1 t+1))=
      Complex.I*((1-(circleMap 0 1 t)^2)/(((2*Real.cos t:ℝ):ℂ)-z)) := by
  have hw : circleMap 0 1 t≠0 := by simp
  rw [deriv_circleMap,unit_circle_polynomial_identity,smul_eq_mul]
  calc
    _=(Complex.I*((1-(circleMap 0 1 t)^2)/(((2*Real.cos t:ℝ):ℂ)-z)))*
        (circleMap 0 1 t*(circleMap 0 1 t)⁻¹) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _=_ := by rw [mul_inv_cancel₀ hw,mul_one]

theorem semicircle_complex_angular_integral (z : ℂ) (hz : 0<z.im) :
    (∫t in (0:ℝ)..2*Real.pi,
      (1-(circleMap 0 1 t)^2)/(((2*Real.cos t:ℝ):ℂ)-z))=
      (2*Real.pi:ℂ)*semicircleRoot z := by
  have hc := semicircle_unit_circle_integral z hz
  simp_rw [circleIntegral,unit_circle_cauchy_integrand z hz] at hc
  rw [intervalIntegral.integral_const_mul] at hc
  apply (mul_left_cancel₀ Complex.I_ne_zero)
  calc
    Complex.I*(∫t in (0:ℝ)..2*Real.pi,
        (1-(circleMap 0 1 t)^2)/(((2*Real.cos t:ℝ):ℂ)-z))=
        (2*Real.pi*Complex.I:ℂ)*semicircleRoot z := hc
    _=Complex.I*((2*Real.pi:ℂ)*semicircleRoot z) := by ring

theorem semicircle_angular_odd_integral (z : ℂ) (_hz : 0<z.im) :
    (∫t in (0:ℝ)..2*Real.pi,
      ((2*Real.sin t*Real.cos t:ℝ):ℂ)/(((2*Real.cos t:ℝ):ℂ)-z))=0 := by
  let f : ℝ→ℂ := fun t => ((2*Real.sin t*Real.cos t:ℝ):ℂ)/(((2*Real.cos t:ℝ):ℂ)-z)
  have href := intervalIntegral.integral_comp_sub_left (f:=f) (a:=(0:ℝ)) (b:=2*Real.pi) (2*Real.pi)
  have hfun : (fun t => f (2*Real.pi-t))=fun t => -f t := by
    funext t
    simp only [f,Real.sin_two_pi_sub,Real.cos_two_pi_sub,Complex.ofReal_mul,Complex.ofReal_neg]
    ring
  rw [hfun,intervalIntegral.integral_neg] at href
  simp only [sub_self,sub_zero] at href
  change (∫t in (0:ℝ)..2*Real.pi,f t)=0
  linear_combination (-1/2:ℂ)*href

/-- The unit-circle calculation in real angular coordinates. -/
theorem semicircle_full_angular_integral (z : ℂ) (hz : 0<z.im) :
    (∫t in (0:ℝ)..2*Real.pi,
      ((Real.sin t^2:ℝ):ℂ)/(((2*Real.cos t:ℝ):ℂ)-z))=
      (Real.pi:ℂ)*semicircleRoot z := by
  have hden := semicircle_angular_denominator_continuous z hz
  have hsin : Continuous (fun t : ℝ => ((Real.sin t^2:ℝ):ℂ)/(((2*Real.cos t:ℝ):ℂ)-z)) := by
    have hn : Continuous (fun t : ℝ => ((Real.sin t^2:ℝ):ℂ)) := by fun_prop
    exact hn.div hden.1 hden.2
  have hodd : Continuous (fun t : ℝ => ((2*Real.sin t*Real.cos t:ℝ):ℂ)/(((2*Real.cos t:ℝ):ℂ)-z)) := by
    have hn : Continuous (fun t : ℝ => ((2*Real.sin t*Real.cos t:ℝ):ℂ)) := by fun_prop
    exact hn.div hden.1 hden.2
  have hdecomp (t : ℝ) :
      (1-(circleMap 0 1 t)^2)/(((2*Real.cos t:ℝ):ℂ)-z)=
        2*(((Real.sin t^2:ℝ):ℂ)/(((2*Real.cos t:ℝ):ℂ)-z))-
          Complex.I*(((2*Real.sin t*Real.cos t:ℝ):ℂ)/(((2*Real.cos t:ℝ):ℂ)-z)) := by
    have hnum : 1-(circleMap 0 1 t)^2=
        2*((Real.sin t^2:ℝ):ℂ)-Complex.I*((2*Real.sin t*Real.cos t:ℝ):ℂ) := by
      have htrig : (Real.cos t:ℂ)^2+(Real.sin t:ℂ)^2=1 := by exact_mod_cast Real.cos_sq_add_sin_sq t
      simp only [circleMap,Complex.ofReal_one,one_mul,zero_add,Complex.exp_mul_I,
        ←Complex.ofReal_cos,←Complex.ofReal_sin,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat]
      linear_combination -htrig-(Real.sin t:ℂ)^2*Complex.I_sq
    rw [hnum,sub_div,mul_div_assoc,mul_div_assoc]
  have hc := semicircle_complex_angular_integral z hz
  simp_rw [hdecomp] at hc
  rw [intervalIntegral.integral_sub
      ((continuous_const.mul hsin).intervalIntegrable (0:ℝ) (2*Real.pi))
      ((continuous_const.mul hodd).intervalIntegrable (0:ℝ) (2*Real.pi)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    semicircle_angular_odd_integral z hz,mul_zero,sub_zero] at hc
  linear_combination (1/2:ℂ)*hc

/-- Half of the full angular integral, using the actual reflection symmetry. -/
theorem semicircle_half_angular_integral (z : ℂ) (hz : 0<z.im) :
    (∫t in (0:ℝ)..Real.pi,
      ((Real.sin t^2:ℝ):ℂ)/(((2*Real.cos t:ℝ):ℂ)-z))=
      ((Real.pi:ℂ)/2)*semicircleRoot z := by
  let f : ℝ→ℂ := fun t => ((Real.sin t^2:ℝ):ℂ)/(((2*Real.cos t:ℝ):ℂ)-z)
  have hden := semicircle_angular_denominator_continuous z hz
  have hcont : Continuous f := by
    have hn : Continuous (fun t : ℝ => ((Real.sin t^2:ℝ):ℂ)) := by fun_prop
    exact hn.div hden.1 hden.2
  have hfun : (fun t => f (2*Real.pi-t))=f := by
    funext t
    simp only [f,Real.sin_two_pi_sub,Real.cos_two_pi_sub,neg_sq]
  have hsecond : (∫t in Real.pi..2*Real.pi,f t)=∫t in (0:ℝ)..Real.pi,f t := by
    calc
      _=(∫t in Real.pi..2*Real.pi,f (2*Real.pi-t)) := by rw [hfun]
      _=(∫t in (2*Real.pi-2*Real.pi)..(2*Real.pi-Real.pi),f t) :=
        intervalIntegral.integral_comp_sub_left _ _
      _=_ := by rw [sub_self,show 2*Real.pi-Real.pi=Real.pi by ring]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ:=volume) (0:ℝ) Real.pi)
    (hcont.intervalIntegrable (μ:=volume) Real.pi (2*Real.pi))
  rw [hsecond] at hsplit
  have hc : (∫t in (0:ℝ)..2*Real.pi,f t)=(Real.pi:ℂ)*semicircleRoot z :=
    semicircle_full_angular_integral z hz
  rw [←hsplit] at hc
  change (∫t in (0:ℝ)..Real.pi,f t)=_
  linear_combination (1/2:ℂ)*hc

end LocalLaw
