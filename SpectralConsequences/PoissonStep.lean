import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.Prod

/-! # The actual Poisson-smoothed indicator and quantitative Cauchy tails -/

open Set MeasureTheory
open scoped Interval
noncomputable section
namespace SpectralConsequences

def poissonStep (η x : ℝ) : ℝ := 1/2+Real.arctan (x/η)/Real.pi

theorem poissonStep_nonnegative (η x : ℝ) : 0 ≤ poissonStep η x := by
  have hh : -(1/2 : ℝ) ≤ Real.arctan (x/η)/Real.pi :=
    (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.neg_pi_div_two_lt_arctan (x/η)])
  unfold poissonStep
  linarith

theorem poissonStep_le_one (η x : ℝ) : poissonStep η x ≤ 1 := by
  have hh : Real.arctan (x/η)/Real.pi ≤ (1/2 : ℝ) :=
    (div_le_iff₀ Real.pi_pos).mpr (by linarith [Real.arctan_lt_pi_div_two (x/η)])
  unfold poissonStep
  linarith

theorem poissonStep_monotone (η : ℝ) (hη : 0 ≤ η) : Monotone (poissonStep η) := by
  intro x y hxy
  exact add_le_add_left (div_le_div_of_nonneg_right
    (Real.arctan_le_arctan (div_le_div_of_nonneg_right hxy hη)) Real.pi_pos.le) _

theorem poissonStep_neg (η x : ℝ) : poissonStep η (-x)=1-poissonStep η x := by
  simp only [poissonStep,neg_div,Real.arctan_neg]
  ring

theorem arctan_le_self_nonnegative (x : ℝ) (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have hint : IntervalIntegrable (fun u : ℝ => (1+u^2)⁻¹) volume 0 x :=
    ((by fun_prop : Continuous (fun u : ℝ => 1+u^2)).inv₀
      (fun u => by nlinarith [sq_nonneg u])).intervalIntegrable _ _
  have hh := intervalIntegral.integral_mono_on hx hint (intervalIntegrable_const (c := (1 : ℝ)))
    (fun u _ => inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg u] : (1 : ℝ) ≤ 1+u^2))
  simpa only [integral_inv_one_add_sq,Real.arctan_zero,sub_zero,intervalIntegral.integral_const,
    sub_zero,smul_eq_mul,mul_one] using hh

theorem poissonStep_right_tail (η h : ℝ) (hη : 0 < η) (hh : 0 < h) :
    1-poissonStep η h ≤ η/(Real.pi*h) := by
  have hident := Real.arctan_inv_of_pos (div_pos hh hη)
  rw [inv_div] at hident
  have heq : 1-poissonStep η h=Real.arctan (η/h)/Real.pi := by
    rw [hident]
    unfold poissonStep
    field_simp [Real.pi_ne_zero]
    ring
  rw [heq]
  exact (div_le_div_of_nonneg_right (arctan_le_self_nonnegative (η/h) (div_nonneg hη.le hh.le))
    Real.pi_pos.le).trans_eq (by rw [div_div,mul_comm h Real.pi])

theorem poissonStep_left_tail (η h : ℝ) (hη : 0 < η) (hh : 0 < h) :
    poissonStep η (-h) ≤ η/(Real.pi*h) := by
  rw [poissonStep_neg]
  exact poissonStep_right_tail η h hη hh

end SpectralConsequences
