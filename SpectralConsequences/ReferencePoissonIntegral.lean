import SpectralConsequences.PoissonTraceIntegral

/-! # Actual compact-support Fubini identities for the reference transform -/

open Set MeasureTheory
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem referencePoisson_point_integral (d : ℕ) (hd : 3 ≤ d)
    (E η : ℝ) (hη : 0 < η) :
    (kestenMcKayStieltjes d ((E : ℂ)+(η : ℂ)*Complex.I)).im/Real.pi=
      ∫x in (-2 : ℝ)..2,kestenMcKayDensity d x*(η/(Real.pi*((E-x)^2+η^2))) := by
  rw [kestenMcKayStieltjes_im_eq_poisson d hd E η hη,←intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [show (x-E)^2=(E-x)^2 by ring]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem referencePoisson_product_integrable (d : ℕ) (hd : 3 ≤ d)
    (η a b : ℝ) (hη : 0 < η) :
    IntegrableOn (fun p : ℝ×ℝ => kestenMcKayDensity d p.2*
      (η/(Real.pi*((p.1-p.2)^2+η^2))))
      (Icc a b ×ˢ Icc (-2 : ℝ) 2) (volume.prod volume) := by
  have hρ : ContinuousOn (fun p : ℝ×ℝ => kestenMcKayDensity d p.2)
      (Icc a b ×ˢ Icc (-2 : ℝ) 2) :=
    (kestenMcKayDensity_continuousOn d hd).comp continuous_snd.continuousOn
      (fun p hp => hp.2)
  have hk : Continuous (fun p : ℝ×ℝ => η/(Real.pi*((p.1-p.2)^2+η^2))) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro p
    exact mul_ne_zero Real.pi_ne_zero (by nlinarith [sq_pos_of_pos hη,sq_nonneg (p.1-p.2)])
  exact (hρ.mul hk.continuousOn).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem referencePoisson_fubini (d : ℕ) (hd : 3 ≤ d)
    (η a b : ℝ) (hη : 0 < η) (hab : a ≤ b) :
    (∫t in a..b,∫x in (-2 : ℝ)..2,kestenMcKayDensity d x*(η/(Real.pi*((t-x)^2+η^2))))=
      ∫x in (-2 : ℝ)..2,∫t in a..b,kestenMcKayDensity d x*(η/(Real.pi*((t-x)^2+η^2))) := by
  have hi : Integrable (Function.uncurry (fun t x : ℝ =>
      kestenMcKayDensity d x*(η/(Real.pi*((t-x)^2+η^2)))))
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc (-2 : ℝ) 2))) := by
    simpa only [Measure.prod_restrict] using referencePoisson_product_integrable d hd η a b hη
  have hh := integral_integral_swap hi
  simpa only [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2),
    integral_Icc_eq_integral_Ioc] using hh

theorem kestenMcKayPoissonCDF_sub_as_integral (d : ℕ) (hd : 3 ≤ d)
    (η a b : ℝ) (hη : 0 < η) (hab : a ≤ b) :
    (∫t in a..b,(kestenMcKayStieltjes d ((t : ℂ)+(η : ℂ)*Complex.I)).im/Real.pi)=
      kestenMcKayPoissonCDF d η b-kestenMcKayPoissonCDF d η a := by
  rw [intervalIntegral.integral_congr (fun t _ => referencePoisson_point_integral d hd t η hη),
    referencePoisson_fubini d hd η a b hη hab]
  have hpoint (x : ℝ) :
      (∫t in a..b,kestenMcKayDensity d x*(η/(Real.pi*((t-x)^2+η^2))))=
        kestenMcKayDensity d x*(poissonStep η (b-x)-poissonStep η (a-x)) := by
    rw [intervalIntegral.integral_const_mul,poisson_integral η x a b hη]
  rw [intervalIntegral.integral_congr (fun x _ => hpoint x)]
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub (kestenMcKayPoisson_integrable d hd η b)
    (kestenMcKayPoisson_integrable d hd η a)]
  rfl

end SpectralConsequences
