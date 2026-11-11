import LocalLaw.SemicircleAngularIntegral

/-! # The actual semicircle density Stieltjes transform

The algebraically selected physical root is identified with the density
integral from Section 2.2 of the article. The proof evaluates a genuine contour
integral and then uses the real substitution x=2 cos(theta).
-/

open Set Complex MeasureTheory
open scoped Real Interval Topology
noncomputable section
namespace LocalLaw

def semicircleDensity (x : ℝ) : ℝ := Real.sqrt (4-x^2)/(2*Real.pi)

theorem semicircleDensity_continuous : Continuous semicircleDensity := by
  unfold semicircleDensity
  fun_prop

theorem semicircleDensity_nonneg (x : ℝ) : 0≤semicircleDensity x := by
  unfold semicircleDensity
  positivity

theorem semicircleDensity_eq_zero_of_not_mem (x : ℝ) (hx : x∉Icc (-2:ℝ) 2) :
    semicircleDensity x=0 := by
  have hsquare : 4-x^2≤0 := by
    simp only [mem_Icc,not_and_or,not_le] at hx
    rcases hx with h|h <;> nlinarith
  simp only [semicircleDensity,Real.sqrt_eq_zero_of_nonpos hsquare,zero_div]

theorem semicircle_sqrt_cos (t : ℝ) (ht : t∈Icc (0:ℝ) Real.pi) :
    Real.sqrt (4-(2*Real.cos t)^2)=2*Real.sin t := by
  have hsin := Real.sin_nonneg_of_mem_Icc ht
  have htrig := Real.cos_sq_add_sin_sq t
  apply (Real.sqrt_eq_iff_eq_sq (by nlinarith) (by positivity)).mpr
  nlinarith

theorem semicircle_kernel_continuous (z : ℂ) (hz : 0<z.im) :
    Continuous (fun x : ℝ => (semicircleDensity x:ℂ)/((x:ℂ)-z)) := by
  exact (Complex.continuous_ofReal.comp semicircleDensity_continuous).div
    (by fun_prop) (fun x => real_sub_upperHalfPlane_ne_zero x hz)

/-- The density Stieltjes integral over its compact support. -/
theorem semicircle_density_interval_integral (z : ℂ) (hz : 0<z.im) :
    (∫x in (-2:ℝ)..2,(semicircleDensity x:ℂ)/((x:ℂ)-z))=semicircleRoot z := by
  let f : ℝ→ℝ := fun t => 2*Real.cos t
  let f' : ℝ→ℝ := fun t => -2*Real.sin t
  let g : ℝ→ℂ := fun x => (semicircleDensity x:ℂ)/((x:ℂ)-z)
  have hderiv : ∀t∈uIcc (0:ℝ) Real.pi,HasDerivAt f (f' t) t := by
    intro t _
    simpa only [f,f',mul_neg,neg_mul] using (Real.hasDerivAt_cos t).const_mul 2
  have hsub := intervalIntegral.integral_comp_smul_deriv hderiv
    (show ContinuousOn f' (uIcc (0:ℝ) Real.pi) from (by fun_prop : Continuous f').continuousOn)
    (semicircle_kernel_continuous z hz)
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
    semicircle_half_angular_integral z hz] at hsub
  have hend0 : f 0=2 := by simp [f]
  have hendpi : f Real.pi= -2 := by simp [f]
  rw [hend0,hendpi,intervalIntegral.integral_symm] at hsub
  change (∫x in (-2:ℝ)..2,g x)=_
  have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hcoef : (-2/(Real.pi:ℂ))*(((Real.pi:ℂ)/2)*semicircleRoot z)= -semicircleRoot z := by
    field_simp
    ring
  rw [hcoef] at hsub
  exact neg_injective hsub.symm

/-- The Stieltjes transform in the article's full-real-line convention. -/
def semicircleStieltjes (z : ℂ) : ℂ :=
  ∫x : ℝ,(semicircleDensity x:ℂ)/((x:ℂ)-z)

theorem semicircleStieltjes_eq_root (z : ℂ) (hz : 0<z.im) :
    semicircleStieltjes z=semicircleRoot z := by
  have hsupport : ∀x:ℝ,x∉Icc (-2:ℝ) 2→(semicircleDensity x:ℂ)/((x:ℂ)-z)=0 := by
    intro x hx
    rw [semicircleDensity_eq_zero_of_not_mem x hx,Complex.ofReal_zero,zero_div]
  have heq := setIntegral_eq_integral_of_forall_compl_eq_zero (μ:=volume) hsupport
  unfold semicircleStieltjes
  rw [←heq,←Measure.restrict_congr_set Ioc_ae_eq_Icc,
    ←intervalIntegral.integral_of_le (by norm_num : (-2:ℝ)≤2)]
  exact semicircle_density_interval_integral z hz

end LocalLaw
