import SpectralConsequences.EmpiricalCDF
import SpectralConsequences.PoissonStep

/-! # Smoothing the actual empirical distribution, including its atoms -/

open scoped BigOperators
noncomputable section
namespace SpectralConsequences
local instance finitePoissonCDFDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def finitePoissonCDF {N : ℕ} (values : Fin N → ℝ) (η E : ℝ) : ℝ :=
  (∑j,poissonStep η (E-values j))/(N : ℝ)

theorem empiricalCDF_eq_indicator_sum {N : ℕ} (values : Fin N → ℝ) (E : ℝ) :
    empiricalCDF values E=(∑j,if values j ≤ E then (1 : ℝ) else 0)/(N : ℝ) := by
  simp [empiricalCDF]

theorem indicator_le_shifted_poissonStep (η h E x : ℝ) (hη : 0 < η) (hh : 0 < h) :
    (if x ≤ E then (1 : ℝ) else 0) ≤ poissonStep η (E+h-x)+η/(Real.pi*h) := by
  have ha : 0 ≤ η/(Real.pi*h) := by positivity
  by_cases hx : x ≤ E
  · rw [if_pos hx]
    have hm := poissonStep_monotone η hη.le (show h ≤ E+h-x by linarith)
    have ht := poissonStep_right_tail η h hη hh
    linarith
  · rw [if_neg hx]
    exact add_nonneg (poissonStep_nonnegative _ _) ha

theorem shifted_poissonStep_le_indicator (η h E x : ℝ) (hη : 0 < η) (hh : 0 < h) :
    poissonStep η (E-h-x) ≤ (if x ≤ E then (1 : ℝ) else 0)+η/(Real.pi*h) := by
  have ha : 0 ≤ η/(Real.pi*h) := by positivity
  by_cases hx : x ≤ E
  · rw [if_pos hx]
    exact (poissonStep_le_one _ _).trans (le_add_of_nonneg_right ha)
  · rw [if_neg hx,zero_add]
    exact (poissonStep_monotone η hη.le (show E-h-x ≤ -h by linarith)).trans
      (poissonStep_left_tail η h hη hh)

theorem empiricalCDF_le_smoothed_right {N : ℕ} (hN : 0 < N) (values : Fin N → ℝ)
    (η h E : ℝ) (hη : 0 < η) (hh : 0 < h) :
    empiricalCDF values E ≤ finitePoissonCDF values η (E+h)+η/(Real.pi*h) := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)))
    (fun j _ => indicator_le_shifted_poissonStep η h E (values j) hη hh)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul] at hsum
  rw [empiricalCDF_eq_indicator_sum]
  have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg N)
  simpa only [finitePoissonCDF,add_div,
    mul_div_cancel_left₀ (η/(Real.pi*h)) (show (N : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))] using hdiv

theorem smoothed_left_le_empiricalCDF {N : ℕ} (hN : 0 < N) (values : Fin N → ℝ)
    (η h E : ℝ) (hη : 0 < η) (hh : 0 < h) :
    finitePoissonCDF values η (E-h) ≤ empiricalCDF values E+η/(Real.pi*h) := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)))
    (fun j _ => shifted_poissonStep_le_indicator η h E (values j) hη hh)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul] at hsum
  rw [empiricalCDF_eq_indicator_sum]
  have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg N)
  simpa only [finitePoissonCDF,add_div,
    mul_div_cancel_left₀ (η/(Real.pi*h)) (show (N : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))] using hdiv

end SpectralConsequences
