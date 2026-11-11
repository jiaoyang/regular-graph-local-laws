import Mathlib

/-!
# Large-N logarithmic parameter growth

These lemmas realize basic numerical side conditions rather than assuming
that polylogarithmic factors are eventually smaller than powers of N.
-/

open Filter Asymptotics

namespace LocalLaw

/-- Every fixed real power of log N is negligible compared with every positive
real power of N. The statement is on the natural sample-size parameter. -/
theorem log_rpow_isLittleO_nat (p s : ℝ) (hs : 0 < s) :
    (fun N : ℕ => Real.log (N : ℝ) ^ p) =o[atTop] fun N : ℕ => (N : ℝ) ^ s := by
  exact (isLittleO_log_rpow_rpow_atTop p hs).comp_tendsto tendsto_natCast_atTop_atTop

/-- The exact log-power inequality used by the polynomial spectral mesh. -/
theorem eventually_log_pow_le_nat (p : ℕ) :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ p ≤ (N : ℝ) := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := p)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hb := h.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb] with N hN
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hnorm : ‖(N : ℝ)‖ = (N : ℝ) := Real.norm_of_nonneg hn
  exact (le_abs_self _).trans (by simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs, abs_of_nonneg hn, one_mul] using hN)

/-- Logarithmic scales eventually exceed any fixed constant. -/
theorem eventually_log_ge_nat (A : ℝ) : ∀ᶠ N : ℕ in atTop, A ≤ Real.log (N : ℝ) := by
  exact (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)).eventually
      (eventually_ge_atTop A)

/-- Fixed constants and real log powers are absorbed by a positive power of N. -/
theorem eventually_const_mul_log_rpow_le (C p s : ℝ) (hs : 0 < s) :
    ∀ᶠ N : ℕ in atTop, C * Real.log (N : ℝ) ^ p ≤ (N : ℝ) ^ s := by
  have hb := ((log_rpow_isLittleO_nat p s hs).const_mul_left C).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb] with N hN
  have hnonneg : 0 ≤ (N : ℝ) ^ s := Real.rpow_nonneg (Nat.cast_nonneg N) s
  exact (le_abs_self _).trans (by
    simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs, abs_of_nonneg hnonneg, one_mul] using hN)

/-- An explicit integer radius with logarithmic growth. -/
noncomputable def logarithmicRadius (β : ℝ) (d N : ℕ) : ℕ :=
  Nat.floor (β * Real.log (N : ℝ) / Real.log ((d - 1 : ℕ) : ℝ))

/-- The localization exponential is controlled by the intended power of N,
including the actual integer rounding. -/
theorem logarithmicRadius_power_bound (β : ℝ) (d N : ℕ)
    (hβ : 0 ≤ β) (hd : 3 ≤ d) (hN : 1 ≤ N) :
    (((d - 1 : ℕ) : ℝ) ^ logarithmicRadius β d N) ≤ (N : ℝ) ^ β := by
  have hb2 : (2 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ d - 1 by omega)
  have hb1 : (1 : ℝ) < ((d - 1 : ℕ) : ℝ) := by linarith
  have hb0 : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogb : 0 < Real.log ((d - 1 : ℕ) : ℝ) := Real.log_pos hb1
  have hexp : 0 ≤ β * Real.log (N : ℝ) / Real.log ((d - 1 : ℕ) : ℝ) :=
    div_nonneg (mul_nonneg hβ (Real.log_nonneg hN1)) hlogb.le
  have hfloor := Nat.floor_le hexp
  change (logarithmicRadius β d N : ℝ) ≤ _ at hfloor
  have hpow := Real.rpow_le_rpow_of_exponent_le hb1.le hfloor
  have hid : ((d - 1 : ℕ) : ℝ) ^
      (β * Real.log (N : ℝ) / Real.log ((d - 1 : ℕ) : ℝ)) = (N : ℝ) ^ β := by
    rw [Real.rpow_def_of_pos hb0, Real.rpow_def_of_pos hN0]
    congr 1
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hlogb)]
    ring
  simpa only [Real.rpow_natCast, hid] using hpow

theorem logarithmicRadius_power_le_N (β : ℝ) (d N : ℕ)
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hd : 3 ≤ d) (hN : 1 ≤ N) :
    (((d - 1 : ℕ) : ℝ) ^ logarithmicRadius β d N) ≤ (N : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow := Real.rpow_le_rpow_of_exponent_le hN1 hβ1
  exact (logarithmicRadius_power_bound β d N hβ hd hN).trans (by simpa using hpow)


/-- Integer rounding loses at most one factor of d-1 in the localization
exponential. This is the lower companion of logarithmicRadius_power_bound. -/
theorem logarithmicRadius_power_lower (β : ℝ) (d N : ℕ)
    (hd : 3 ≤ d) (hN : 1 ≤ N) :
    (N : ℝ) ^ β ≤ ((d - 1 : ℕ) : ℝ) *
      (((d - 1 : ℕ) : ℝ) ^ logarithmicRadius β d N) := by
  have hb1 : (1 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < d - 1 by omega)
  have hb0 : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogb : 0 < Real.log ((d - 1 : ℕ) : ℝ) := Real.log_pos hb1
  have hfloor := Nat.lt_floor_add_one (β * Real.log (N : ℝ) / Real.log ((d - 1 : ℕ) : ℝ))
  change β * Real.log (N : ℝ) / Real.log ((d - 1 : ℕ) : ℝ) <
    (logarithmicRadius β d N : ℝ) + 1 at hfloor
  have hp := Real.rpow_le_rpow_of_exponent_le hb1.le hfloor.le
  have hid : ((d - 1 : ℕ) : ℝ) ^
      (β * Real.log (N : ℝ) / Real.log ((d - 1 : ℕ) : ℝ)) = (N : ℝ) ^ β := by
    rw [Real.rpow_def_of_pos hb0, Real.rpow_def_of_pos hN0]
    congr 1
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hlogb)]
    ring
  simpa only [hid, Real.rpow_add hb0, Real.rpow_natCast, Real.rpow_one, mul_comm] using hp

theorem logarithmicRadius_inverse_bound (β : ℝ) (d N : ℕ)
    (hd : 3 ≤ d) (hN : 1 ≤ N) :
    ((((d - 1 : ℕ) : ℝ) ^ logarithmicRadius β d N))⁻¹ ≤
      ((d - 1 : ℕ) : ℝ) / (N : ℝ) ^ β := by
  have hb0 : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
  have hB : (0 : ℝ) < (((d - 1 : ℕ) : ℝ) ^ logarithmicRadius β d N) := by positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow := logarithmicRadius_power_lower β d N hd hN
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hN0 β)).mpr
  calc
    _ ≤ ((((d - 1 : ℕ) : ℝ) ^ logarithmicRadius β d N))⁻¹ *
        (((d - 1 : ℕ) : ℝ) * (((d - 1 : ℕ) : ℝ) ^ logarithmicRadius β d N)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = ((d - 1 : ℕ) : ℝ) := by
      rw [mul_left_comm, inv_mul_cancel₀ (ne_of_gt hB), mul_one]

/-- The local approximation term satisfies every fixed logarithmic
smallness budget eventually for any positive logarithmic radius exponent. -/
theorem eventually_localization_log_budget (β : ℝ) (d m : ℕ)
    (hβ : 0 < β) (hd : 3 ≤ d) :
    ∀ᶠ N : ℕ in atTop,
      ((((d - 1 : ℕ) : ℝ) ^ logarithmicRadius β d N))⁻¹ ≤
        1 / (3 * Real.log (N : ℝ) ^ m) := by
  have hsmall := eventually_const_mul_log_rpow_le (3 * ((d - 1 : ℕ) : ℝ)) (m : ℝ) β hβ
  filter_upwards [hsmall, eventually_log_ge_nat 1, eventually_ge_atTop 1] with N hsmall hlog hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNp : 0 < (N : ℝ) ^ β := Real.rpow_pos_of_pos hN0 β
  have hLp : 0 < Real.log (N : ℝ) := by linarith
  have hsmall' : 3 * ((d - 1 : ℕ) : ℝ) * Real.log (N : ℝ) ^ m ≤ (N : ℝ) ^ β := by
    simpa only [Real.rpow_natCast] using hsmall
  apply (logarithmicRadius_inverse_bound β d N hd hN).trans
  apply (div_le_div_iff₀ hNp (by positivity : 0 < 3 * Real.log (N : ℝ) ^ m)).mpr
  nlinarith


end LocalLaw
