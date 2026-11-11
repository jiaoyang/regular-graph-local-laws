import LocalLaw.ParameterGrowth

/-!
# Integer resampling radii and the small-ball sampling budget

An integer radius of order log log N has a ball-size bound which is eventually
smaller than N/4. The proof includes the rounding and changes of exponential
base; it does not assume a polylogarithmic cardinality conclusion.
-/

open Filter

namespace LocalLaw

noncomputable def doubleLogRadius (a d N : ℕ) : ℕ :=
  Nat.floor (((2 * a : ℕ) : ℝ) * Real.log (Real.log (N : ℝ)) /
    Real.log ((d - 1 : ℕ) : ℝ))

noncomputable def resamplingGrowthExponent (a d : ℕ) : ℝ :=
  (((2 * a : ℕ) : ℝ) * Real.log ((d + 1 : ℕ) : ℝ)) / Real.log ((d - 1 : ℕ) : ℝ)

theorem doubleLogRadius_power_bound (a d N : ℕ) (hd : 3 ≤ d)
    (hlog : 1 ≤ Real.log (N : ℝ)) :
    (((d + 1 : ℕ) : ℝ) ^ doubleLogRadius a d N) ≤
      Real.log (N : ℝ) ^ resamplingGrowthExponent a d := by
  have hbase : (1 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < d - 1 by omega)
  have hlogbase : 0 < Real.log ((d - 1 : ℕ) : ℝ) := Real.log_pos hbase
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hexp : 0 ≤ (((2 * a : ℕ) : ℝ) * Real.log (Real.log (N : ℝ)) /
      Real.log ((d - 1 : ℕ) : ℝ)) := by
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hlog)
    · exact hlogbase.le
  have hfloor := Nat.floor_le hexp
  change (doubleLogRadius a d N : ℝ) ≤ _ at hfloor
  have hplus : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ d + 1 by omega)
  have hpluspos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hplus hfloor
  have hid : ((d + 1 : ℕ) : ℝ) ^
      ((((2 * a : ℕ) : ℝ) * Real.log (Real.log (N : ℝ))) / Real.log ((d - 1 : ℕ) : ℝ)) =
      Real.log (N : ℝ) ^ resamplingGrowthExponent a d := by
    rw [Real.rpow_def_of_pos hpluspos, Real.rpow_def_of_pos hlogpos]
    congr 1
    unfold resamplingGrowthExponent
    ring
  simpa only [Real.rpow_natCast, hid] using hpow

/-- The deterministic sampling small-set hypothesis is eventually realized
by the actual log-log integer radius. -/
theorem eventually_resampling_ball_budget (a d : ℕ) (hd : 3 ≤ d) :
    ∀ᶠ N : ℕ in atTop, 4 * (d + 1) ^ doubleLogRadius a d N ≤ N := by
  have hsmall := eventually_const_mul_log_rpow_le 4 (resamplingGrowthExponent a d) 1 (by norm_num)
  filter_upwards [hsmall, eventually_log_ge_nat 1] with N hN hlog
  have hp := doubleLogRadius_power_bound a d N hd hlog
  have hr : (4 : ℝ) * (((d + 1 : ℕ) : ℝ) ^ doubleLogRadius a d N) ≤ (N : ℝ) := by
    have hbound : (4 : ℝ) * Real.log (N : ℝ) ^ resamplingGrowthExponent a d ≤ (N : ℝ) := by
      simpa only [Real.rpow_one] using hN
    exact (mul_le_mul_of_nonneg_left hp (by norm_num)).trans hbound
  exact_mod_cast hr

end LocalLaw
