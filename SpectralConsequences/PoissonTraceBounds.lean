import SpectralConsequences.ReferencePoissonIntegral
import SpectralConsequences.PoissonCDFBounds

/-! # Trace errors bound the genuine smoothed distribution increments -/

open Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem finiteTrace_height_continuous {N : ℕ} (values : Fin N → ℝ)
    (η : ℝ) (hη : 0 < η) :
    Continuous (fun t : ℝ => (finiteStieltjes values ((t : ℂ)+(η : ℂ)*Complex.I)).im/Real.pi) := by
  have hpoint : (fun t : ℝ => (finiteStieltjes values ((t : ℂ)+(η : ℂ)*Complex.I)).im/Real.pi)=
      (fun t : ℝ => ((N : ℝ)⁻¹*∑j,η/((values j-t)^2+η^2))/Real.pi) := by
    funext t
    rw [finiteStieltjes_im]
  rw [hpoint]
  have hc (j : Fin N) : Continuous (fun t : ℝ => η/((values j-t)^2+η^2)) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro t
    nlinarith [sq_pos_of_pos hη,sq_nonneg (values j-t)]
  exact (continuous_const.mul (continuous_finset_sum _ (fun j _ => hc j))).div_const Real.pi

theorem referenceTrace_height_intervalIntegrable (d : ℕ) (hd : 3 ≤ d)
    (η a b : ℝ) (hη : 0 < η) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ =>
      (kestenMcKayStieltjes d ((t : ℂ)+(η : ℂ)*Complex.I)).im/Real.pi) volume a b := by
  have hi : Integrable (fun p : ℝ×ℝ =>
      kestenMcKayDensity d p.2*(η/(Real.pi*((p.1-p.2)^2+η^2))))
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc (-2 : ℝ) 2))) := by
    simpa only [Measure.prod_restrict] using referencePoisson_product_integrable d hd η a b hη
  have hp := hi.integral_prod_left
  have heq (t : ℝ) :
      (∫x in Icc (-2 : ℝ) 2,kestenMcKayDensity d x*(η/(Real.pi*((t-x)^2+η^2))))=
        (kestenMcKayStieltjes d ((t : ℂ)+(η : ℂ)*Complex.I)).im/Real.pi := by
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
    exact (referencePoisson_point_integral d hd t η hη).symm
  have hIcc : IntegrableOn (fun t : ℝ =>
      (kestenMcKayStieltjes d ((t : ℂ)+(η : ℂ)*Complex.I)).im/Real.pi) (Icc a b) :=
    hp.congr (ae_of_all _ heq)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hIcc

theorem smoothed_increment_error {N : ℕ} (values : Fin N → ℝ)
    (d : ℕ) (hd : 3 ≤ d) (η a b t : ℝ) (hη : 0 < η) (hab : a ≤ b)
    (htrace : ∀ E ∈ Icc a b,
      ‖finiteStieltjes values ((E : ℂ)+(η : ℂ)*Complex.I)-
        kestenMcKayStieltjes d ((E : ℂ)+(η : ℂ)*Complex.I)‖ ≤ t) :
    |(finitePoissonCDF values η b-finitePoissonCDF values η a)-
      (kestenMcKayPoissonCDF d η b-kestenMcKayPoissonCDF d η a)| ≤ (t/Real.pi)*(b-a) := by
  rw [←finitePoissonCDF_sub_as_integral values η a b hη,
    ←kestenMcKayPoissonCDF_sub_as_integral d hd η a b hη hab]
  rw [←intervalIntegral.integral_sub
    ((finiteTrace_height_continuous values η hη).intervalIntegrable a b)
    (referenceTrace_height_intervalIntegrable d hd η a b hη hab)]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun E : ℝ => (finiteStieltjes values ((E : ℂ)+(η : ℂ)*Complex.I)).im/Real.pi-
      (kestenMcKayStieltjes d ((E : ℂ)+(η : ℂ)*Complex.I)).im/Real.pi)
    (a := a) (b := b) (C := t/Real.pi) (by
      intro E hE
      have hIoc : E ∈ Ioc a b := by simpa only [uIoc_of_le hab] using hE
      have hnorm := Complex.abs_im_le_norm
        (finiteStieltjes values ((E : ℂ)+(η : ℂ)*Complex.I)-
          kestenMcKayStieltjes d ((E : ℂ)+(η : ℂ)*Complex.I))
      have hbound := hnorm.trans (htrace E ⟨hIoc.1.le,hIoc.2⟩)
      simp only [Complex.sub_im] at hbound
      simpa only [Real.norm_eq_abs,←sub_div,abs_div,abs_of_pos Real.pi_pos] using
        div_le_div_of_nonneg_right hbound Real.pi_pos.le)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] using hh

end SpectralConsequences
