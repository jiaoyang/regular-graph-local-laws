import SpectralConsequences.KestenMcKayPoissonCDF
import SpectralConsequences.FiniteResolventSpectrum

/-! # Exact Poisson trace identities for empirical and reference spectra -/

open Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem finitePoissonCDF_sub_as_integral {N : ℕ} (values : Fin N → ℝ)
    (η a b : ℝ) (hη : 0 < η) :
    (∫t in a..b,(finiteStieltjes values ((t : ℂ)+(η : ℂ)*Complex.I)).im/Real.pi)=
      finitePoissonCDF values η b-finitePoissonCDF values η a := by
  have hpoint (t : ℝ) :
      (finiteStieltjes values ((t : ℂ)+(η : ℂ)*Complex.I)).im/Real.pi=
        (∑j,η/(Real.pi*((t-values j)^2+η^2)))/(N : ℝ) := by
    rw [finiteStieltjes_im]
    have heach (j : Fin N) : η/(Real.pi*((t-values j)^2+η^2))=
        (η/((values j-t)^2+η^2))/Real.pi := by
      rw [div_div]
      congr 1
      ring
    have hsum : (∑j,η/(Real.pi*((t-values j)^2+η^2)))=
        (∑j,η/((values j-t)^2+η^2))/Real.pi := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun j _ => heach j)
    rw [hsum]
    simp only [div_eq_mul_inv]
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hpoint t),intervalIntegral.integral_div]
  rw [intervalIntegral.integral_finset_sum (fun j _ =>
    (poissonKernel_continuous η (values j) hη).intervalIntegrable a b)]
  simp_rw [poisson_integral η _ a b hη]
  rw [Finset.sum_sub_distrib,sub_div]
  rfl

theorem kestenMcKayStieltjes_im_eq_poisson (d : ℕ) (hd : 3 ≤ d)
    (E η : ℝ) (hη : 0 < η) :
    (kestenMcKayStieltjes d ((E : ℂ)+(η : ℂ)*Complex.I)).im=
      ∫x in (-2 : ℝ)..2,kestenMcKayDensity d x*(η/((x-E)^2+η^2)) := by
  let z : ℂ := (E : ℂ)+(η : ℂ)*Complex.I
  have hz : 0 < z.im := by simpa only [z,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
    Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] using hη
  have hc : ContinuousOn (fun x : ℝ => (kestenMcKayDensity d x : ℂ)/((x : ℂ)-z))
      (Icc (-2 : ℝ) 2) :=
    (Complex.continuous_ofReal.continuousOn.comp (kestenMcKayDensity_continuousOn d hd)
      (fun _ _ => mem_univ _)).div
      (by fun_prop : Continuous (fun x : ℝ => (x : ℂ)-z)).continuousOn
      (fun x _ => real_sub_complex_ne_zero x z hz)
  have hint : IntervalIntegrable
      (fun x : ℝ => (kestenMcKayDensity d x : ℂ)/((x : ℂ)-z)) volume (-2 : ℝ) 2 :=
    hc.intervalIntegrable_of_Icc (by norm_num)
  have hh := Complex.imCLM.intervalIntegral_comp_comm hint
  change (∫x in (-2 : ℝ)..2,((kestenMcKayDensity d x : ℂ)/((x : ℂ)-z)).im)=
    (∫x in (-2 : ℝ)..2,(kestenMcKayDensity d x : ℂ)/((x : ℂ)-z)).im at hh
  rw [kestenMcKay_density_interval_integral d hd z hz,
    ←kestenMcKayStieltjes_eq_transform d hd z hz] at hh
  calc
    _=(∫x in (-2 : ℝ)..2,((kestenMcKayDensity d x : ℂ)/((x : ℂ)-z)).im) := hh.symm
    _=_ := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [div_eq_mul_inv,Complex.mul_im]
      simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
      dsimp only [z]
      rw [inverse_real_sub_im]

end SpectralConsequences
