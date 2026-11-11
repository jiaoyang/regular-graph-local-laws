import LocalLaw.SemicircleStieltjes

/-! # The semicircle integral at any strictly small quadratic root

The real exterior spectral parameters are needed for the rational density
decomposition of the Kesten--McKay law. No upper-half-plane assumption is used
here: exclusion of the support and the strictly small root are explicit.
-/

open Set Complex Metric MeasureTheory
open scoped Real Interval Topology
noncomputable section
namespace LocalLaw

theorem physical_root_unit_circle_integral (m z : ℂ)
    (heq : m^2+z*m+1=0) (hm : ‖m‖<1) :
    (∮w in C(0,1),(1-w^2)/(w^2-z*w+1))=(2*Real.pi*Complex.I:ℂ)*m := by
  have hm0 := cavity_root_ne_zero heq
  have hlinear := cavity_quadratic_linear_identity heq
  have hden : ∀w∈closedBall (0:ℂ) 1,w+m⁻¹≠0 :=
    fun w hw => cavity_circle_outer_denominator_ne_zero hm0 hm w hw
  let f : ℂ→ℂ := fun w => (1-w^2)/(w+m⁻¹)
  have hf : DifferentiableOn ℂ f (closedBall (0:ℂ) 1) := by
    intro w hw
    exact (((differentiableAt_const (1:ℂ)).sub (differentiableAt_id.pow 2)).div
      (differentiableAt_id.add_const (m⁻¹)) (hden w hw)).differentiableWithinAt
  have hmem : -m∈ball (0:ℂ) 1 := by simpa only [mem_ball,dist_zero_right,norm_neg] using hm
  have hc := hf.circleIntegral_sub_inv_smul hmem
  have hfactor (w:ℂ) : w^2-z*w+1=(w+m)*(w+m⁻¹) := by rw [hlinear]; field_simp; ring
  have hsame : (fun w : ℂ => (w- -m)⁻¹ • f w)=fun w => (1-w^2)/(w^2-z*w+1) := by
    funext w
    rw [hfactor]
    simp only [f,sub_neg_eq_add,smul_eq_mul,div_eq_mul_inv,mul_inv_rev]
    ring
  have hfroot : f (-m)=m := by
    apply (div_eq_iff (hden (-m) (ball_subset_closedBall hmem))).mpr
    field_simp
    ring
  rw [hsame,hfroot,smul_eq_mul] at hc
  exact hc

theorem real_cos_scaled_mem_support (t : ℝ) : 2*Real.cos t∈Icc (-2:ℝ) 2 := by
  constructor <;> nlinarith [Real.neg_one_le_cos t,Real.cos_le_one t]

theorem angular_cauchy_integrand_without_spectral_assumption (z : ℂ) (t : ℝ) :
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

theorem angular_odd_integral_zero (z : ℂ) :
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

theorem physical_root_angular_integral (m z : ℂ)
    (heq : m^2+z*m+1=0) (hm : ‖m‖<1)
    (hden : ∀x∈Icc (-2:ℝ) 2,(x:ℂ)-z≠0) :
    (∫t in (0:ℝ)..Real.pi,((Real.sin t^2:ℝ):ℂ)/(((2*Real.cos t:ℝ):ℂ)-z))=
      ((Real.pi:ℂ)/2)*m := by
  have hc := physical_root_unit_circle_integral m z heq hm
  simp_rw [circleIntegral,angular_cauchy_integrand_without_spectral_assumption] at hc
  rw [intervalIntegral.integral_const_mul] at hc
  have hc' : (∫t in (0:ℝ)..2*Real.pi,(1-(circleMap 0 1 t)^2)/(((2*Real.cos t:ℝ):ℂ)-z))=
      (2*Real.pi:ℂ)*m := by
    apply (mul_left_cancel₀ Complex.I_ne_zero)
    calc _=(2*Real.pi*Complex.I:ℂ)*m := hc
         _=_ := by ring
  have hD : Continuous (fun t : ℝ => ((2*Real.cos t:ℝ):ℂ)-z) := by fun_prop
  have hDn : ∀t : ℝ,((2*Real.cos t:ℝ):ℂ)-z≠0 := fun t => hden _ (real_cos_scaled_mem_support t)
  let f : ℝ→ℂ := fun t => ((Real.sin t^2:ℝ):ℂ)/(((2*Real.cos t:ℝ):ℂ)-z)
  have hsin : Continuous f := by
    have hn : Continuous (fun t : ℝ => ((Real.sin t^2:ℝ):ℂ)) := by fun_prop
    exact hn.div hD hDn
  have hodd : Continuous (fun t : ℝ => ((2*Real.sin t*Real.cos t:ℝ):ℂ)/(((2*Real.cos t:ℝ):ℂ)-z)) := by
    have hn : Continuous (fun t : ℝ => ((2*Real.sin t*Real.cos t:ℝ):ℂ)) := by fun_prop
    exact hn.div hD hDn
  have hdecomp (t : ℝ) : (1-(circleMap 0 1 t)^2)/(((2*Real.cos t:ℝ):ℂ)-z)=
      2*f t-Complex.I*(((2*Real.sin t*Real.cos t:ℝ):ℂ)/(((2*Real.cos t:ℝ):ℂ)-z)) := by
    have hnum : 1-(circleMap 0 1 t)^2=
        2*((Real.sin t^2:ℝ):ℂ)-Complex.I*((2*Real.sin t*Real.cos t:ℝ):ℂ) := by
      have htrig : (Real.cos t:ℂ)^2+(Real.sin t:ℂ)^2=1 := by exact_mod_cast Real.cos_sq_add_sin_sq t
      simp only [circleMap,Complex.ofReal_one,one_mul,zero_add,Complex.exp_mul_I,
        ←Complex.ofReal_cos,←Complex.ofReal_sin,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat]
      linear_combination -htrig-(Real.sin t:ℂ)^2*Complex.I_sq
    rw [hnum,sub_div,mul_div_assoc,mul_div_assoc]
  simp_rw [hdecomp] at hc'
  rw [intervalIntegral.integral_sub
      ((continuous_const.mul hsin).intervalIntegrable (0:ℝ) (2*Real.pi))
      ((continuous_const.mul hodd).intervalIntegrable (0:ℝ) (2*Real.pi)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    angular_odd_integral_zero z,mul_zero,sub_zero] at hc'
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
    (hsin.intervalIntegrable (μ:=volume) (0:ℝ) Real.pi)
    (hsin.intervalIntegrable (μ:=volume) Real.pi (2*Real.pi))
  rw [hsecond] at hsplit
  rw [←hsplit] at hc'
  change (∫t in (0:ℝ)..Real.pi,f t)=_
  linear_combination (1/4:ℂ)*hc'

/-- The same density integral at any parameter outside the support with a
strictly small quadratic root, including real exterior parameters. -/
theorem physical_root_density_interval_integral (m z : ℂ)
    (heq : m^2+z*m+1=0) (hm : ‖m‖<1)
    (hden : ∀x∈Icc (-2:ℝ) 2,(x:ℂ)-z≠0) :
    (∫x in (-2:ℝ)..2,(semicircleDensity x:ℂ)/((x:ℂ)-z))=m := by
  let f : ℝ→ℝ := fun t => 2*Real.cos t
  let f' : ℝ→ℝ := fun t => -2*Real.sin t
  let g : ℝ→ℂ := fun x => (semicircleDensity x:ℂ)/((x:ℂ)-z)
  have hderiv : ∀t∈uIcc (0:ℝ) Real.pi,HasDerivAt f (f' t) t := by
    intro t _
    simpa only [f,f',mul_neg,neg_mul] using (Real.hasDerivAt_cos t).const_mul 2
  have hg : ContinuousOn g (f ''uIcc (0:ℝ) Real.pi) := by
    apply ((Complex.continuous_ofReal.comp semicircleDensity_continuous).continuousOn.div
      (by fun_prop : Continuous (fun x : ℝ => (x:ℂ)-z)).continuousOn hden).mono
    rintro x ⟨t,_,rfl⟩
    exact real_cos_scaled_mem_support t
  have hsub := intervalIntegral.integral_comp_smul_deriv' hderiv
    (show ContinuousOn f' (uIcc (0:ℝ) Real.pi) from (by fun_prop : Continuous f').continuousOn) hg
  have hpoint : EqOn (fun t => f' t • (g∘f) t)
      (fun t => (-2/(Real.pi:ℂ))*(((Real.sin t^2:ℝ):ℂ)/(((2*Real.cos t:ℝ):ℂ)-z)))
      (uIcc (0:ℝ) Real.pi) := by
    intro t ht
    have ht' : t∈Icc (0:ℝ) Real.pi := by simpa only [uIcc_of_le Real.pi_pos.le] using ht
    simp only [f,f',g,Function.comp_apply,semicircleDensity,semicircle_sqrt_cos t ht',
      Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_neg,
      Complex.ofReal_ofNat]
    ring
  rw [intervalIntegral.integral_congr hpoint,intervalIntegral.integral_const_mul,
    physical_root_angular_integral m z heq hm hden] at hsub
  have hend0 : f 0=2 := by simp [f]
  have hendpi : f Real.pi= -2 := by simp [f]
  rw [hend0,hendpi,intervalIntegral.integral_symm] at hsub
  have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hcoef : (-2/(Real.pi:ℂ))*(((Real.pi:ℂ)/2)*m)= -m := by field_simp; ring
  rw [hcoef] at hsub
  exact neg_injective hsub.symm

end LocalLaw
