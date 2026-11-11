import SpectralConsequences.KestenMcKayPoissonCDF

/-! # Positive smoothed distributions and their compact-support left tails -/

open Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem finitePoissonCDF_nonnegative {N : ℕ} (values : Fin N → ℝ) (η E : ℝ) :
    0 ≤ finitePoissonCDF values η E :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => poissonStep_nonnegative _ _)) (Nat.cast_nonneg _)

theorem finitePoissonCDF_left_tail {N : ℕ} (hN : 0 < N) (values : Fin N → ℝ)
    (M η : ℝ) (hη : 0 < η) (hlower : ∀j,-M ≤ values j) :
    finitePoissonCDF values η (-M-1) ≤ η/Real.pi := by
  have htail : poissonStep η (-1) ≤ η/Real.pi := by
    simpa only [mul_one] using poissonStep_left_tail η 1 hη (by norm_num)
  have hpoint (j : Fin N) : poissonStep η (-M-1-values j) ≤ η/Real.pi :=
    (poissonStep_monotone η hη.le (by linarith [hlower j] : -M-1-values j ≤ -1)).trans htail
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N))) (fun j _ => hpoint j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  unfold finitePoissonCDF
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  nlinarith only [hsum]

theorem kestenMcKayPoissonCDF_nonnegative (d : ℕ) (hd : 3 ≤ d) (η E : ℝ) :
    0 ≤ kestenMcKayPoissonCDF d η E := by
  apply intervalIntegral.integral_nonneg (by norm_num : (-2 : ℝ) ≤ 2)
  intro x _
  exact mul_nonneg (kestenMcKayDensity_nonnegative d hd x) (poissonStep_nonnegative _ _)

theorem kestenMcKayPoissonCDF_left_tail (d : ℕ) (hd : 3 ≤ d)
    (M η : ℝ) (hM : 2 ≤ M) (hη : 0 < η) :
    kestenMcKayPoissonCDF d η (-M-1) ≤ η/Real.pi := by
  have htail : poissonStep η (-1) ≤ η/Real.pi := by
    simpa only [mul_one] using poissonStep_left_tail η 1 hη (by norm_num)
  have hi := (kestenMcKayDensity_intervalIntegrable d hd).mul_const (η/Real.pi)
  have hh := intervalIntegral.integral_mono_on (by norm_num : (-2 : ℝ) ≤ 2)
    (kestenMcKayPoisson_integrable d hd η (-M-1)) hi
    (fun x hx => mul_le_mul_of_nonneg_left
      ((poissonStep_monotone η hη.le (show -M-1-x ≤ -1 by linarith [hx.1])).trans htail)
      (kestenMcKayDensity_nonnegative d hd x))
  rw [intervalIntegral.integral_mul_const,kestenMcKayDensity_integral d hd,one_mul] at hh
  exact hh

end SpectralConsequences
