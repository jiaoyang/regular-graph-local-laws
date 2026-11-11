import LocalLaw.UniformGraphNet
import LocalLaw.ParameterGrowth

/-!
# Polynomial exceptional densities below the nominal source error

An exponent strictly below 1-beta absorbs every fixed logarithmic loss.
The nominal paper error supplies its own geometric lower bound, without
changing the radius in the discontinuous error inflation branch.
-/

open Filter
namespace LocalLaw

theorem graphPaperError_nominal_ge_inverse_power (a d N : ℕ) (β : ℝ) (z : ℂ)
    (hd : 3 ≤ d) (hβ : 0 ≤ β) (hN : 1 ≤ N) (hL : 1 ≤ Real.log (N : ℝ)) (hz : 0 ≤ z.im) :
    ((N : ℝ) ^ β)⁻¹ ≤ graphPaperError a d N (logarithmicRadius β d N) z := by
  have hk : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
  have hpow := logarithmicRadius_power_bound β d N hβ hd hN
  have hinv : ((N : ℝ) ^ β)⁻¹ ≤ (((d - 1 : ℕ) : ℝ) ^ logarithmicRadius β d N)⁻¹ :=
    by simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hpow
  apply hinv.trans
  apply le_trans _ (graphPaperError_lower a d N _ z hL hz)
  unfold localizationErrorFloor
  have hone : 1 ≤ Real.log (N : ℝ) ^ (8 * a) := one_le_pow₀ hL
  exact le_mul_of_one_le_left (by positivity) hone

/-- Every fixed multiple of N^(gamma-1) is smaller than nominal epsilon
with any fixed number of inverse logarithms. -/
theorem eventually_polynomial_density_absorbed (a d p : ℕ) (β γ K : ℝ)
    (hd : 3 ≤ d) (hβ : 0 ≤ β) (hgap : γ + β < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 ≤ z.im →
      K * (N : ℝ) ^ γ / (N : ℝ) ≤
        graphPaperError a d N (logarithmicRadius β d N) z / Real.log (N : ℝ) ^ p := by
  filter_upwards [eventually_const_mul_log_rpow_le K (p : ℝ) (1 - γ - β) (by linarith),
    eventually_log_ge_nat 1, eventually_ge_atTop 1] with N hnum hL hN
  intro z hz
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hLp : 0 < Real.log (N : ℝ) := by linarith
  have hNb : 0 < (N : ℝ) ^ β := Real.rpow_pos_of_pos hn β
  have hNg : 0 < (N : ℝ) ^ γ := Real.rpow_pos_of_pos hn γ
  have hε := graphPaperError_nominal_ge_inverse_power a d N β z hd hβ hN hL hz
  have hid : (N : ℝ) ^ (1 - γ - β) * (N : ℝ) ^ γ * (N : ℝ) ^ β = (N : ℝ) := by
    rw [← Real.rpow_add hn, ← Real.rpow_add hn]
    convert Real.rpow_one (N : ℝ) using 2
    ring
  have hscaled : (K * Real.log (N : ℝ) ^ p) * (N : ℝ) ^ γ * (N : ℝ) ^ β ≤ (N : ℝ) := by
    apply le_trans _ (le_of_eq hid)
    apply mul_le_mul_of_nonneg_right _ hNb.le
    apply mul_le_mul_of_nonneg_right _ hNg.le
    simpa only [Real.rpow_natCast] using hnum
  apply (le_div_iff₀ (pow_pos hLp p)).mpr
  apply (mul_le_mul_right hn).mp
  have hbase : (K * (N : ℝ) ^ γ) * Real.log (N : ℝ) ^ p ≤ ((N : ℝ) ^ β)⁻¹ * (N : ℝ) := by
    apply (mul_le_mul_right hNb).mp
    calc
      _ = (K * Real.log (N : ℝ) ^ p) * (N : ℝ) ^ γ * (N : ℝ) ^ β := by ring
      _ ≤ (N : ℝ) := hscaled
      _ = (((N : ℝ) ^ β)⁻¹ * (N : ℝ)) * (N : ℝ) ^ β := by field_simp
  have hright := mul_le_mul_of_nonneg_right hε hn.le
  have heq : K * (N : ℝ) ^ γ / (N : ℝ) * Real.log (N : ℝ) ^ p * (N : ℝ) =
      (K * (N : ℝ) ^ γ) * Real.log (N : ℝ) ^ p := by field_simp
  simpa only [heq] using hbase.trans hright

end LocalLaw
