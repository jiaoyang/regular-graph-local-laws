import Mathlib

/-! # Absorb fixed probability constants by one spare sample-size exponent -/

namespace LocalLaw

theorem const_div_pow_succ_le (C : ℝ) (N p : ℕ) (hN : 1 ≤ N) (hC : C ≤ (N : ℝ)) :
    C / (N : ℝ) ^ (p + 1) ≤ 1 / (N : ℝ) ^ p := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  apply (div_le_div_iff₀ (pow_pos hNp _) (pow_pos hNp _)).mpr
  rw [pow_succ, one_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hC (pow_nonneg hNp.le p)

theorem eventually_const_div_pow_succ_le (C : ℝ) (p : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop, C / (N : ℝ) ^ (p + 1) ≤ 1 / (N : ℝ) ^ p := by
  filter_upwards [Filter.eventually_ge_atTop (max 1 ⌈C⌉₊)] with N hN
  have hC : C ≤ (N : ℝ) := (Nat.le_ceil C).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hN))
  exact const_div_pow_succ_le C N p ((le_max_left _ _).trans hN) hC

theorem all_nat_polynomial_bounds_real (condition : ℕ → Prop) (failure : ℕ → ℝ)
    (h : ∀ p : ℕ, ∀ᶠ N : ℕ in Filter.atTop, condition N → failure N ≤ 1 / (N : ℝ) ^ p) :
    ∀ p : ℝ, ∀ᶠ N : ℕ in Filter.atTop, condition N → failure N ≤ 1 / (N : ℝ) ^ p := by
  intro p
  filter_upwards [h ⌈p⌉₊, Filter.eventually_ge_atTop 1] with N hbound hN
  intro hcondition
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hp : (N : ℝ) ^ p ≤ (N : ℝ) ^ ⌈p⌉₊ := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hNr (Nat.le_ceil p)
  exact (hbound hcondition).trans (one_div_le_one_div_of_le (Real.rpow_pos_of_pos hNp p) hp)

end LocalLaw
