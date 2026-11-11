import LocalLaw.ParameterGrowth

/-!
# Polynomial probability decay from packed-cycle moments

A fixed positive power gap beats every logarithmic factor. Choosing the
moment order explicitly turns a bound 2*(C log(N)^m/N^gap)^q into N^(-p).
The moment estimate itself must come from the graph-counting proof.
-/

namespace LocalLaw

noncomputable def sufficientMomentOrder (gap : ℝ) (p : ℕ) : ℕ :=
  ⌈2 * ((p + 1 : ℕ) : ℝ) / gap⌉₊

theorem sufficientMomentOrder_bound (gap : ℝ) (p : ℕ) (hgap : 0 < gap) :
    ((p + 1 : ℕ) : ℝ) ≤ (sufficientMomentOrder gap p : ℝ) * gap / 2 := by
  have h := Nat.le_ceil (2 * ((p + 1 : ℕ) : ℝ) / gap)
  have hh := (div_le_iff₀ hgap).mp h
  change 2 * ((p + 1 : ℕ) : ℝ) ≤ (sufficientMomentOrder gap p : ℝ) * gap at hh
  linarith

/-- All numerical large-N conditions for a polynomial moment tail are proved,
with the moment order's exponent requirement explicit. -/
theorem eventually_polylog_moment_decay (C gap : ℝ) (m q p : ℕ)
    (hC : 0 ≤ C) (hgap : 0 < gap)
    (hq : ((p + 1 : ℕ) : ℝ) ≤ (q : ℝ) * gap / 2) :
    ∀ᶠ N : ℕ in Filter.atTop,
      2 * (C * Real.log (N : ℝ) ^ m / (N : ℝ) ^ gap) ^ q ≤ 1 / (N : ℝ) ^ p := by
  have hsmall := eventually_const_mul_log_rpow_le C (m : ℝ) (gap / 2) (by linarith)
  filter_upwards [hsmall, Filter.eventually_ge_atTop 2, eventually_log_ge_nat 1]
    with N hsmall hN hlog
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn₁ : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn₂ : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hhalf : 0 < (N : ℝ) ^ (gap / 2) := Real.rpow_pos_of_pos hn _
  have hfull : 0 < (N : ℝ) ^ gap := Real.rpow_pos_of_pos hn _
  have hsmall' : C * Real.log (N : ℝ) ^ m ≤ (N : ℝ) ^ (gap / 2) := by
    simpa only [Real.rpow_natCast] using hsmall
  have hpow : (N : ℝ) ^ gap = (N : ℝ) ^ (gap / 2) * (N : ℝ) ^ (gap / 2) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  have hbase : C * Real.log (N : ℝ) ^ m / (N : ℝ) ^ gap ≤ 1 / (N : ℝ) ^ (gap / 2) := by
    apply (div_le_div_iff₀ hfull hhalf).mpr
    calc
      _ ≤ (N : ℝ) ^ (gap / 2) * (N : ℝ) ^ (gap / 2) :=
        mul_le_mul_of_nonneg_right hsmall' hhalf.le
      _ = 1 * (N : ℝ) ^ gap := by rw [← hpow, one_mul]
  have hp := pow_le_pow_left₀ (show 0 ≤ C * Real.log (N : ℝ) ^ m / (N : ℝ) ^ gap by positivity) hbase q
  have hpowq : ((N : ℝ) ^ (gap / 2)) ^ q = (N : ℝ) ^ ((q : ℝ) * gap / 2) := by
    rw [← Real.rpow_natCast _ q, ← Real.rpow_mul hn.le]
    congr 1
    ring
  have hexp : (N : ℝ) ^ (p + 1) ≤ (N : ℝ) ^ ((q : ℝ) * gap / 2) := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hn₁ hq
  calc
    _ ≤ 2 * (1 / (N : ℝ) ^ (gap / 2)) ^ q := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 2 / (N : ℝ) ^ ((q : ℝ) * gap / 2) := by rw [one_div_pow, hpowq]; ring
    _ ≤ 2 / (N : ℝ) ^ (p + 1) :=
      div_le_div_of_nonneg_left (by norm_num) (pow_pos hn _) hexp
    _ ≤ (N : ℝ) / (N : ℝ) ^ (p + 1) := div_le_div_of_nonneg_right hn₂ (by positivity)
    _ = 1 / (N : ℝ) ^ p := by rw [pow_succ]; field_simp [ne_of_gt hn]; ring

/-- An explicit integer moment order suffices for each requested polynomial
failure exponent. No additional asymptotic-tail premise remains. -/
theorem eventually_chosen_moment_decay (C gap : ℝ) (m p : ℕ) (hC : 0 ≤ C) (hgap : 0 < gap) :
    ∀ᶠ N : ℕ in Filter.atTop,
      2 * (C * Real.log (N : ℝ) ^ m / (N : ℝ) ^ gap) ^ sufficientMomentOrder gap p ≤
        1 / (N : ℝ) ^ p :=
  eventually_polylog_moment_decay C gap m _ p hC hgap (sufficientMomentOrder_bound gap p hgap)

end LocalLaw
