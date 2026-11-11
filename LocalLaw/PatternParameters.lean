import LocalLaw.PatternSwitchingProbability
import LocalLaw.ParameterGrowth

/-!
# Numerical control of the switching-pattern denominator

The actual switching slack is logarithmic when the required pattern has
O(log N) edges. Its cumulative correction through all pattern edges is
bounded by two, with every finite-N and eventual inequality derived here.
-/

namespace LocalLaw

/-- A denominator loses at most a factor two after K steps when its total
relative loss is at most one half. This is a finite Bernoulli inequality. -/
theorem denominator_inflation_le_two (A s : ℝ) (K : ℕ)
    (hA : 0 < A) (hs : 0 ≤ s) (hK : 1 ≤ K) (hbudget : 2 * (K : ℝ) * s ≤ A) :
    0 < A - s ∧ (A / (A - s)) ^ K ≤ 2 := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hsA : 2 * s ≤ A := by nlinarith [mul_le_mul_of_nonneg_right hKr hs]
  have hgap : 0 < A - s := by linarith
  let x := s / A
  have hx : 0 ≤ x := div_nonneg hs hA.le
  have hxhalf : x ≤ 1 / 2 := by
    dsimp [x]
    apply (div_le_iff₀ hA).mpr
    linarith
  have hKx : (K : ℝ) * x ≤ 1 / 2 := by
    dsimp [x]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hA).mpr
    linarith
  have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ -x by linarith) K
  have hhalf : (1 / 2 : ℝ) ≤ (1 - x) ^ K := by
    have hid : 1 + (K : ℝ) * (-x) = 1 - (K : ℝ) * x := by ring
    rw [hid, show 1 + -x = 1 - x by ring] at hbern
    linarith
  have hinv : 1 / (1 - x) ^ K ≤ (2 : ℝ) := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hhalf
    norm_num at h ⊢
    exact h
  refine ⟨hgap, ?_⟩
  have hid : A / (A - s) = 1 / (1 - x) := by
    dsimp [x]
    field_simp
  rw [hid, one_div_pow]
  exact hinv

/-- The actual natural-valued switching denominator is positive and its
cumulative normalization loss is uniformly bounded. -/
theorem pattern_switching_denominator_control (N d K : ℕ)
    (hN : 0 < N) (hd : 0 < d) (hK : 1 ≤ K)
    (hbudget : 2 * K * RegularGraph.patternSwitchSlack d K ≤ N * d) :
    0 < N * d - RegularGraph.patternSwitchSlack d K ∧
      (((N : ℝ) * (d : ℝ)) / ((N * d - RegularGraph.patternSwitchSlack d K : ℕ) : ℝ)) ^ K ≤ 2 := by
  have hle : RegularGraph.patternSwitchSlack d K ≤ N * d := by nlinarith
  have hr : 2 * (K : ℝ) * (RegularGraph.patternSwitchSlack d K : ℝ) ≤ (N : ℝ) * (d : ℝ) := by
    exact_mod_cast hbudget
  have hh := denominator_inflation_le_two ((N : ℝ) * (d : ℝ)) (RegularGraph.patternSwitchSlack d K) K
    (mul_pos (Nat.cast_pos.mpr hN) (Nat.cast_pos.mpr hd)) (Nat.cast_nonneg _) hK hr
  have hpos : 0 < N * d - RegularGraph.patternSwitchSlack d K := by
    have hposR : (0 : ℝ) < ((N * d - RegularGraph.patternSwitchSlack d K : ℕ) : ℝ) := by
      rw [Nat.cast_sub hle, Nat.cast_mul]
      exact hh.1
    exact Nat.cast_pos.mp hposR
  refine ⟨hpos, ?_⟩
  rw [Nat.cast_sub hle, Nat.cast_mul]
  exact hh.2

/-- Every O(log N)-edge pattern satisfies the actual cumulative slack budget
uniformly in its edge count for all sufficiently large N. -/
theorem eventually_pattern_switching_budget (d : ℕ) (C D : ℝ) (hd : 0 < d)
    (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ K : ℕ,
      (K : ℝ) ≤ C * Real.log (N : ℝ) + D →
        2 * K * RegularGraph.patternSwitchSlack d K ≤ N * d := by
  let A : ℝ := C + D
  let B : ℝ := 2 * (d : ℝ) * ((d : ℝ) + 2) + 2 * A
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsmall := eventually_const_mul_log_rpow_le (2 * A * B) 2 1 (by norm_num)
  filter_upwards [hsmall, eventually_log_ge_nat 1] with N hsmall hlog
  intro K hK
  have hL : 0 ≤ Real.log (N : ℝ) := by linarith
  have hKr : (K : ℝ) ≤ A * Real.log (N : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hlog hD
    dsimp [A]
    nlinarith
  have hslack : (RegularGraph.patternSwitchSlack d K : ℝ) ≤ B * Real.log (N : ℝ) := by
    have hconst : 0 ≤ 2 * (d : ℝ) * ((d : ℝ) + 2) := by positivity
    have hh := mul_le_mul_of_nonneg_left hlog hconst
    unfold RegularGraph.patternSwitchSlack
    push_cast
    dsimp [B]
    nlinarith
  have hprod := mul_le_mul hKr hslack (Nat.cast_nonneg _) (mul_nonneg hA hL)
  have hsmall' : 2 * A * B * Real.log (N : ℝ) ^ 2 ≤ (N : ℝ) := by
    simpa only [Real.rpow_two, Real.rpow_one] using hsmall
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hNd : (N : ℝ) ≤ (N : ℝ) * (d : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hdR (show (0 : ℝ) ≤ N from Nat.cast_nonneg N)
  have hfinal : 2 * (K : ℝ) * (RegularGraph.patternSwitchSlack d K : ℝ) ≤ (N : ℝ) * (d : ℝ) := by
    calc
      _ ≤ 2 * (A * Real.log (N : ℝ) * (B * Real.log (N : ℝ))) :=
        by nlinarith only [hprod]
      _ = 2 * A * B * Real.log (N : ℝ) ^ 2 := by ring
      _ ≤ (N : ℝ) := hsmall'
      _ ≤ (N : ℝ) * (d : ℝ) := hNd
  exact_mod_cast hfinal

end LocalLaw
