import SpectralConsequences.PoissonStep

/-! # Exact integration of the Poisson kernel at positive height -/

open MeasureTheory Set
noncomputable section
namespace SpectralConsequences

theorem poissonStep_shift_hasDerivAt (η x t : ℝ) (hη : 0 < η) :
    HasDerivAt (fun u : ℝ => poissonStep η (u-x))
      (η/(Real.pi*((t-x)^2+η^2))) t := by
  have h := (((Real.hasDerivAt_arctan ((t-x)/η)).comp t
    (((hasDerivAt_id t).sub_const x).div_const η)).div_const Real.pi).const_add (1/2 : ℝ)
  have hden : 1+((t-x)/η)^2 ≠ 0 := by positivity
  have hden' : (t-x)^2+η^2 ≠ 0 := by nlinarith [sq_pos_of_pos hη,sq_nonneg (t-x)]
  convert h using 1
  dsimp only [id_eq]
  field_simp [Real.pi_ne_zero,hη.ne',hden,hden']
  ring

theorem poissonKernel_continuous (η x : ℝ) (hη : 0 < η) :
    Continuous (fun t : ℝ => η/(Real.pi*((t-x)^2+η^2))) := by
  apply Continuous.div continuous_const (by fun_prop)
  intro t
  exact mul_ne_zero Real.pi_ne_zero (by nlinarith [sq_pos_of_pos hη,sq_nonneg (t-x)])

theorem poisson_integral (η x a b : ℝ) (hη : 0 < η) :
    (∫t in a..b,η/(Real.pi*((t-x)^2+η^2)))=
      poissonStep η (b-x)-poissonStep η (a-x) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    exact poissonStep_shift_hasDerivAt η x t hη
  · exact (poissonKernel_continuous η x hη).intervalIntegrable _ _

end SpectralConsequences
