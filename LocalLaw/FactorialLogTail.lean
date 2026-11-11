import LocalLaw.CorrelationSampling
import LocalLaw.SamplingCollisionFactorial

/-!
# Polynomial tails from a bounded mean and ceil(log N) matching order

A fixed integer K gives q!>=K^(q-K). Choosing K above the required constant
mean times exp(p+1) proves the actual inverse-N^p tail eventually. No Stirling
estimate, assumed tail budget, or smallness of the constant mean is needed.
-/

open Filter
namespace LocalLaw

/-- A fixed lower factorial slope, sufficient for the logarithmic tail. -/
theorem factorial_ge_fixed_power (K q : ℕ) (hq : K ≤ q) :
    K ^ (q - K) ≤ Nat.factorial q := by
  have hh := Nat.factorial_mul_pow_sub_le_factorial hq
  exact (Nat.le_mul_of_pos_left _ (Nat.factorial_pos K)).trans hh

theorem bounded_mean_factorial_comparison (C : ℝ) (hC : 0 ≤ C) (K q : ℕ)
    (hK : 0 < K) (hq : K ≤ q) :
    C ^ q / (Nat.factorial q : ℝ) ≤ (K : ℝ) ^ K * (C / K) ^ q := by
  have hKp : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hden : (K : ℝ) ^ (q - K) ≤ (Nat.factorial q : ℝ) := by
    exact_mod_cast factorial_ge_fixed_power K q hq
  apply (div_le_div_of_nonneg_left (pow_nonneg hC q) (pow_pos hKp _) hden).trans_eq
  have hdecomp : (K : ℝ) ^ q = (K : ℝ) ^ K * (K : ℝ) ^ (q - K) := by
    rw [← pow_add, Nat.add_sub_of_le hq]
  rw [div_pow, hdecomp]
  field_simp
  ring

/-- A bounded (possibly large) collision mean has every polynomial tail at
matching order ceil(log N), with its numerical largeness derived. -/
theorem eventually_bounded_mean_factorial_tail (p : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, 0 ≤ x → x ≤ C →
      x ^ Nat.ceil (Real.log (N : ℝ)) / (Nat.factorial (Nat.ceil (Real.log (N : ℝ))) : ℝ) ≤
        1 / (N : ℝ) ^ p := by
  let K : ℕ := Nat.ceil (C * Real.exp ((p : ℝ) + 1)) + 1
  have hK : 0 < K := by dsimp only [K]; omega
  have hKp : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hKbound : C * Real.exp ((p : ℝ) + 1) ≤ (K : ℝ) := by
    have hh := Nat.le_ceil (C * Real.exp ((p : ℝ) + 1))
    have hle : Nat.ceil (C * Real.exp ((p : ℝ) + 1)) ≤ K := by dsimp only [K]; omega
    exact hh.trans (Nat.cast_le.mpr hle)
  have hratio : C / (K : ℝ) ≤ Real.exp (-((p + 1 : ℕ) : ℝ)) := by
    apply (div_le_iff₀ hKp).mpr
    have hh := mul_le_mul_of_nonneg_left hKbound (Real.exp_pos (-((p + 1 : ℕ) : ℝ))).le
    have hid : Real.exp (-((p + 1 : ℕ) : ℝ)) * (C * Real.exp ((p : ℝ) + 1)) = C := by
      calc
        _ = C * (Real.exp (-((p + 1 : ℕ) : ℝ)) * Real.exp ((p : ℝ) + 1)) := by ring
        _ = C := by
          rw [← Real.exp_add]
          have he : -((p + 1 : ℕ) : ℝ) + ((p : ℝ) + 1) = 0 := by push_cast; ring
          rw [he, Real.exp_zero, mul_one]
    rw [hid] at hh
    exact hh.trans_eq (by ring)
  filter_upwards [eventually_log_ge_nat (K : ℝ), eventually_ge_atTop (K ^ K),
    eventually_ge_atTop 1] with N hlogK hNK hN
  intro x hx hxC
  let q := Nat.ceil (Real.log (N : ℝ))
  have hq : K ≤ q := by
    have hh := hlogK.trans (Nat.le_ceil (Real.log (N : ℝ)))
    exact_mod_cast hh
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hpref : (K : ℝ) ^ K ≤ N := by exact_mod_cast hNK
  have hgeo := ceil_log_power_le_inverse_power (C / K) N (p + 1) (by omega)
    (div_nonneg hC hKp.le) hratio
  calc
    _ ≤ C ^ q / (Nat.factorial q : ℝ) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxC _) (by positivity)
    _ ≤ (K : ℝ) ^ K * (C / K) ^ q := bounded_mean_factorial_comparison C hC K q hK hq
    _ ≤ (K : ℝ) ^ K * (1 / (N : ℝ) ^ (p + 1)) := mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ ≤ (N : ℝ) * (1 / (N : ℝ) ^ (p + 1)) := mul_le_mul_of_nonneg_right hpref (by positivity)
    _ = _ := by rw [pow_succ]; field_simp; ring

end LocalLaw
