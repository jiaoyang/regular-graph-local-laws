import LocalLaw.UniformGraphNet
import LocalLaw.ParameterGrowth

/-!
# Numerical absorption of explicit exceptional-center densities

A polynomial exceptional count is compared with the actual localization term,
including integer rounding of r. Its exponent condition is explicit. This
module does not assert a random-graph exceptional-count estimate.
-/

namespace LocalLaw

/-- The radius exponential dominates a sparse density whenever gamma+beta<=1. -/
theorem sparse_density_le_localization (N d : ℕ) (β γ : ℝ) (bad : ℕ)
    (hN : 1 ≤ N) (hd : 3 ≤ d) (hβ : 0 ≤ β) (hexp : γ + β ≤ 1)
    (hbad : (bad : ℝ) ≤ (N : ℝ) ^ γ) :
    (bad : ℝ) / (N : ℝ) ≤
      ((((d - 1 : ℕ) : ℝ) ^ logarithmicRadius β d N))⁻¹ := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnp : (0 : ℝ) < N := by linarith
  have hp : 0 < (N : ℝ) ^ β := Real.rpow_pos_of_pos hnp β
  have hproduct : (N : ℝ) ^ γ * (N : ℝ) ^ β ≤ (N : ℝ) := by
    rw [← Real.rpow_add hnp]
    have h := Real.rpow_le_rpow_of_exponent_le hn hexp
    simpa only [Real.rpow_one] using h
  have hdensity : (bad : ℝ) / (N : ℝ) ≤ 1 / (N : ℝ) ^ β := by
    apply (div_le_div_iff₀ hnp hp).mpr
    calc
      (bad : ℝ) * (N : ℝ) ^ β ≤ (N : ℝ) ^ γ * (N : ℝ) ^ β :=
        mul_le_mul_of_nonneg_right hbad hp.le
      _ ≤ 1 * (N : ℝ) := by simpa only [one_mul] using hproduct
  have hr := logarithmicRadius_power_bound β d N hβ hd hN
  have hkpos : 0 < (((d - 1 : ℕ) : ℝ) ^ logarithmicRadius β d N) := by
    have hk : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
    positivity
  exact hdensity.trans (by simpa only [one_div] using one_div_le_one_div_of_le hkpos hr)

/-- Sparse errors fit an arbitrary fixed logarithmic tolerance of the actual
paper error. The needed exponent and fixed-constant conditions are numerical. -/
theorem sparse_error_log_absorption (N d a p : ℕ) (β γ C M : ℝ) (bad : ℕ)
    (hN : 1 ≤ N) (hd : 3 ≤ d) (hβ : 0 ≤ β) (hexp : γ + β ≤ 1)
    (hbad : (bad : ℝ) ≤ (N : ℝ) ^ γ) (hC : 0 < C) (hM : 0 ≤ M)
    (hL : 1 ≤ Real.log (N : ℝ)) (hp : p + 1 ≤ 8 * a)
    (hconstant : C * M ≤ Real.log (N : ℝ)) (z : ℂ) (hz : 0 ≤ z.im) :
    ((bad : ℝ) / (N : ℝ)) * M ≤
      graphPaperError a d N (logarithmicRadius β d N) z /
        (C * Real.log (N : ℝ) ^ p) := by
  let L := Real.log (N : ℝ)
  let δ := ((((d - 1 : ℕ) : ℝ) ^ logarithmicRadius β d N))⁻¹
  have hLp : 0 < L := by dsimp [L]; linarith
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hdensity := sparse_density_le_localization N d β γ bad hN hd hβ hexp hbad
  have hpow := pow_le_pow_right₀ hL hp
  have hnum : C * M * L ^ p ≤ L ^ (8 * a) := by
    calc
      C * M * L ^ p ≤ L * L ^ p := mul_le_mul_of_nonneg_right hconstant (by positivity)
      _ = L ^ (p + 1) := by ring
      _ ≤ L ^ (8 * a) := hpow
  have hε := graphPaperError_lower a d N (logarithmicRadius β d N) z hL hz
  apply (le_div_iff₀ (mul_pos hC (pow_pos hLp p))).mpr
  calc
    ((bad : ℝ) / (N : ℝ)) * M * (C * L ^ p) ≤ δ * M * (C * L ^ p) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdensity hM) (by positivity)
    _ = (C * M * L ^ p) * δ := by ring
    _ ≤ L ^ (8 * a) * δ := mul_le_mul_of_nonneg_right hnum hδ
    _ ≤ graphPaperError a d N (logarithmicRadius β d N) z := hε

/-- Every fixed exceptional-value constant is eventually absorbed. -/
theorem eventually_sparse_cavity_absorption (a d : ℕ) (β γ M : ℝ)
    (ha : 1 ≤ a) (hd : 3 ≤ d) (hβ : 0 ≤ β) (hexp : γ + β ≤ 1) (hM : 0 ≤ M) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ bad : ℕ, (bad : ℝ) ≤ (N : ℝ) ^ γ →
      ∀ z : ℂ, 0 ≤ z.im →
        ((bad : ℝ) / (N : ℝ)) * M ≤
          graphPaperError a d N (logarithmicRadius β d N) z /
            (2 * Real.log (N : ℝ) ^ 2) := by
  filter_upwards [Filter.eventually_ge_atTop 1, eventually_log_ge_nat 1,
    eventually_log_ge_nat (2 * M)] with N hN hL hconstant
  intro bad hbad z hz
  exact sparse_error_log_absorption N d a 2 β γ 2 M bad hN hd hβ hexp hbad
    (by norm_num) hM hL (by omega) hconstant z hz

/-- A strengthened exceptional-count exponent 7c/8 is compatible with every
printed localization exponent beta<=c/32, including its endpoint. Proving
that strengthened graph count is a separate geometric/probability task. -/
theorem strengthened_sparse_exponent (c β : ℝ) (hc : c < 1) (hβ : β ≤ c / 32) :
    7 * c / 8 + β ≤ 1 := by linarith

end LocalLaw
