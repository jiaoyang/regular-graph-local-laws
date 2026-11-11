import SpectralConsequences.KestenMcKayCDF
import SpectralConsequences.FinitePoissonCDF
import SpectralConsequences.PoissonIntegral

/-! # Poisson smoothing of the actual Kesten--McKay probability density -/

open Set MeasureTheory
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance kestenPoissonCDFDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def kestenMcKayPoissonCDF (d : ℕ) (η E : ℝ) : ℝ :=
  ∫ x in (-2 : ℝ)..2,kestenMcKayDensity d x*poissonStep η (E-x)

theorem poissonStep_continuous (η : ℝ) : Continuous (poissonStep η) := by
  exact continuous_const.add
    ((Real.continuous_arctan.comp (continuous_id.div_const η)).div_const Real.pi)

theorem kestenMcKayPoisson_integrable (d : ℕ) (hd : 3 ≤ d) (η E : ℝ) :
    IntervalIntegrable (fun x => kestenMcKayDensity d x*poissonStep η (E-x))
      volume (-2 : ℝ) 2 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  exact (kestenMcKayDensity_continuousOn d hd).mul
    ((poissonStep_continuous η).comp (by fun_prop)).continuousOn

theorem kestenMcKay_indicator_integrable (d : ℕ) (hd : 3 ≤ d) (E : ℝ) :
    IntervalIntegrable (fun x => kestenMcKayDensity d x*(if x ≤ E then (1 : ℝ) else 0))
      volume (-2 : ℝ) 2 := by
  have heq : (fun x => kestenMcKayDensity d x*(if x ≤ E then (1 : ℝ) else 0))=
      (Iic E).indicator (kestenMcKayDensity d) := by
    funext x
    by_cases hx : x ≤ E <;> simp [hx]
  rw [heq]
  exact ⟨(kestenMcKayDensity_intervalIntegrable d hd).1.indicator measurableSet_Iic,
    (kestenMcKayDensity_intervalIntegrable d hd).2.indicator measurableSet_Iic⟩

theorem kestenMcKayCDF_eq_indicator_integral (d : ℕ) (hd : 3 ≤ d) (E : ℝ) :
    kestenMcKayCDF d E=
      ∫ x in (-2 : ℝ)..2,kestenMcKayDensity d x*(if x ≤ E then (1 : ℝ) else 0) := by
  by_cases hE : E ∈ Icc (-2 : ℝ) 2
  · have heq : (fun x => kestenMcKayDensity d x*(if x ≤ E then (1 : ℝ) else 0))=
        (Iic E).indicator (kestenMcKayDensity d) := by
      funext x
      by_cases hx : x ≤ E <;> simp [hx]
    rw [heq,kestenMcKayCDF,kestenMcKayClip_eq hE]
    exact (intervalIntegral.integral_indicator (f := kestenMcKayDensity d) (μ := volume) hE).symm
  · simp only [mem_Icc,not_and_or,not_le] at hE
    rcases hE with hlo|hhi
    · rw [kestenMcKayCDF_below d E hlo.le]
      have heq : EqOn
          (fun x => kestenMcKayDensity d x*(if x ≤ E then (1 : ℝ) else 0))
          (fun _ => 0) (uIcc (-2 : ℝ) 2) := by
        intro x hx
        have hxcc : x ∈ Icc (-2 : ℝ) 2 := by
          simpa only [uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 2)] using hx
        simp only [if_neg (show ¬x ≤ E by linarith [hxcc.1]),mul_zero]
      rw [intervalIntegral.integral_congr heq,intervalIntegral.integral_zero]
    · rw [kestenMcKayCDF_above d hd E hhi.le]
      have heq : EqOn
          (fun x => kestenMcKayDensity d x*(if x ≤ E then (1 : ℝ) else 0))
          (kestenMcKayDensity d) (uIcc (-2 : ℝ) 2) := by
        intro x hx
        have hxcc : x ∈ Icc (-2 : ℝ) 2 := by
          simpa only [uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 2)] using hx
        have hx2 : x ≤ 2 := hxcc.2
        simp only [if_pos (by linarith : x ≤ E),mul_one]
      rw [intervalIntegral.integral_congr heq,kestenMcKayDensity_integral d hd]

theorem kestenMcKayCDF_le_smoothed_right (d : ℕ) (hd : 3 ≤ d)
    (η h E : ℝ) (hη : 0 < η) (hh : 0 < h) :
    kestenMcKayCDF d E ≤ kestenMcKayPoissonCDF d η (E+h)+η/(Real.pi*h) := by
  let a := η/(Real.pi*h)
  have hi := kestenMcKayPoisson_integrable d hd η (E+h)
  have ha := (kestenMcKayDensity_intervalIntegrable d hd).mul_const a
  have hbound := intervalIntegral.integral_mono_on (by norm_num : (-2 : ℝ) ≤ 2)
    (kestenMcKay_indicator_integrable d hd E) (hi.add ha)
    (by
      intro x _
      simpa only [mul_add] using (mul_le_mul_of_nonneg_left
        (indicator_le_shifted_poissonStep η h E x hη hh) (kestenMcKayDensity_nonnegative d hd x)))
  rw [←kestenMcKayCDF_eq_indicator_integral d hd E] at hbound
  have heq : (∫x in (-2 : ℝ)..2,kestenMcKayDensity d x*poissonStep η (E+h-x)+
      kestenMcKayDensity d x*a)=kestenMcKayPoissonCDF d η (E+h)+a := by
    rw [intervalIntegral.integral_add hi ha,intervalIntegral.integral_mul_const,
      kestenMcKayDensity_integral d hd,one_mul]
    rfl
  exact hbound.trans_eq heq

theorem kestenMcKay_smoothed_left_le_CDF (d : ℕ) (hd : 3 ≤ d)
    (η h E : ℝ) (hη : 0 < η) (hh : 0 < h) :
    kestenMcKayPoissonCDF d η (E-h) ≤ kestenMcKayCDF d E+η/(Real.pi*h) := by
  let a := η/(Real.pi*h)
  have hi := kestenMcKay_indicator_integrable d hd E
  have ha := (kestenMcKayDensity_intervalIntegrable d hd).mul_const a
  have hbound := intervalIntegral.integral_mono_on (by norm_num : (-2 : ℝ) ≤ 2)
    (kestenMcKayPoisson_integrable d hd η (E-h)) (hi.add ha)
    (by
      intro x _
      simpa only [mul_add] using (mul_le_mul_of_nonneg_left
        (shifted_poissonStep_le_indicator η h E x hη hh) (kestenMcKayDensity_nonnegative d hd x)))
  have heq : (∫x in (-2 : ℝ)..2,kestenMcKayDensity d x*(if x ≤ E then (1 : ℝ) else 0)+
      kestenMcKayDensity d x*a)=kestenMcKayCDF d E+a := by
    rw [intervalIntegral.integral_add hi ha,←kestenMcKayCDF_eq_indicator_integral d hd E,
      intervalIntegral.integral_mul_const,kestenMcKayDensity_integral d hd,one_mul]
  exact hbound.trans_eq heq

end SpectralConsequences
