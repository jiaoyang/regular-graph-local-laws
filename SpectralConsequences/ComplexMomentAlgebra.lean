import Mathlib

/-! # The complex polynomial used in the high-moment integration by parts

Conjugation is retained explicitly. In particular the test polynomial is not
an ordinary odd power of a complex residual.
-/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences

/-- The test function whose product with z is the 2p-th absolute moment. -/
def complexMomentTest (p : ℕ) (z : ℂ) : ℂ := z^(p-1) * (starRingEnd ℂ z)^p

theorem complexMomentTest_norm (p : ℕ) (z : ℂ) :
    ‖complexMomentTest p z‖ = ‖z‖^(2*p-1) := by
  simp only [complexMomentTest, norm_mul, norm_pow, Complex.norm_conj, ← pow_add]
  congr 1
  omega

theorem complexMomentTest_energy (p : ℕ) (hp : 1 ≤ p) (z : ℂ) :
    z * complexMomentTest p z = (‖z‖^(2*p) : ℝ) := by
  have he : z * complexMomentTest p z = z^p * (starRingEnd ℂ z)^p := by
    unfold complexMomentTest
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hp]
  rw [he, ← mul_pow, Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq, ← pow_mul]

/-- A uniform disk bound gives the exact degree-n Lipschitz polynomial. -/
theorem complex_norm_pow_sub_pow_le (x y : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (n : ℕ) :
    ‖x^n-y^n‖ ≤ (n:ℝ)*‖x-y‖*R^(n-1) := by
  have hid := geom_sum₂_mul x y n
  rw [← hid, norm_mul]
  have hsum : ‖∑ i ∈ Finset.range n, x^i * y^(n-1-i)‖ ≤ (n:ℝ)*R^(n-1) := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, ‖x^i*y^(n-1-i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range n, R^(n-1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i < n := Finset.mem_range.mp hi
        rw [norm_mul, norm_pow, norm_pow]
        calc
          _ ≤ R^i * R^(n-1-i) := mul_le_mul
            (pow_le_pow_left₀ (norm_nonneg x) hx _) (pow_le_pow_left₀ (norm_nonneg y) hy _)
            (pow_nonneg (norm_nonneg y) _) (pow_nonneg hR _)
          _ = R^(n-1) := by rw [← pow_add];congr 1;omega
      _ = _ := by simp [nsmul_eq_mul]
  have hh := mul_le_mul_of_nonneg_right hsum (norm_nonneg (x-y))
  nlinarith only [hh]

/-- A product of two powers has the expected total-degree Lipschitz bound. -/
theorem complex_monomial_difference_bound (a b : ℕ) (x y : ℂ)
    (R : ℝ) (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖x^a*(starRingEnd ℂ x)^b-y^a*(starRingEnd ℂ y)^b‖ ≤
      ((a+b:ℕ):ℝ)*‖x-y‖*R^(a+b-1) := by
  rcases a with _ | a
  · simpa only [pow_zero, one_mul, zero_add, ← map_sub, Complex.norm_conj] using
      complex_norm_pow_sub_pow_le (starRingEnd ℂ x) (starRingEnd ℂ y) R hR
        (by simpa only [Complex.norm_conj] using hx)
        (by simpa only [Complex.norm_conj] using hy) b
  rcases b with _ | b
  · simpa only [pow_zero, mul_one, add_zero] using complex_norm_pow_sub_pow_le x y R hR hx hy (a+1)
  have ha := complex_norm_pow_sub_pow_le x y R hR hx hy (a+1)
  have hb := complex_norm_pow_sub_pow_le (starRingEnd ℂ x) (starRingEnd ℂ y) R hR
    (by simpa only [Complex.norm_conj] using hx)
    (by simpa only [Complex.norm_conj] using hy) (b+1)
  simp only [← map_sub, Complex.norm_conj, Nat.add_sub_cancel] at hb
  simp only [Nat.add_sub_cancel] at ha
  have hid : x^(a+1)*(starRingEnd ℂ x)^(b+1)-y^(a+1)*(starRingEnd ℂ y)^(b+1) =
      (x^(a+1)-y^(a+1))*(starRingEnd ℂ x)^(b+1) +
        y^(a+1)*((starRingEnd ℂ x)^(b+1)-(starRingEnd ℂ y)^(b+1)) := by ring
  rw [hid]
  calc
    _ ≤ ‖x^(a+1)-y^(a+1)‖ * ‖x‖^(b+1) +
        ‖y‖^(a+1) * ‖(starRingEnd ℂ x)^(b+1)-(starRingEnd ℂ y)^(b+1)‖ := by
      simpa only [norm_mul, norm_pow, Complex.norm_conj] using norm_add_le
        ((x^(a+1)-y^(a+1))*(starRingEnd ℂ x)^(b+1))
        (y^(a+1)*((starRingEnd ℂ x)^(b+1)-(starRingEnd ℂ y)^(b+1)))
    _ ≤ ((a+1:ℕ):ℝ)*‖x-y‖*R^a*R^(b+1) +
        R^(a+1)*(((b+1:ℕ):ℝ)*‖x-y‖*R^b) := by
      apply add_le_add
      · exact mul_le_mul ha (pow_le_pow_left₀ (norm_nonneg x) hx _)
          (pow_nonneg (norm_nonneg x) _) (by positivity)
      · exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg y) hy _) hb
          (norm_nonneg _) (pow_nonneg hR _)
    _ = _ := by
      simp only [pow_succ, Nat.cast_add, Nat.cast_one]
      have hex : a+1+(b+1)-1 = a+b+1 := by omega
      rw [hex, pow_add, pow_succ]
      ring

/-- An expansion around x controls the moment-test difference by the residual
increment and a nonnegative polynomial. -/
theorem complexMomentTest_difference_bound (p : ℕ) (hp : 1 ≤ p) (x y : ℂ) :
    ‖complexMomentTest p x-complexMomentTest p y‖ ≤
      ((2*p-1:ℕ):ℝ)*‖x-y‖*(‖x‖+‖x-y‖)^(2*p-2) := by
  have hR : 0 ≤ ‖x‖+‖x-y‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hx : ‖x‖ ≤ ‖x‖+‖x-y‖ := le_add_of_nonneg_right (norm_nonneg _)
  have hy : ‖y‖ ≤ ‖x‖+‖x-y‖ := by
    have hh := norm_sub_le_norm_sub_add_norm_sub y x 0
    simpa only [sub_zero, norm_sub_rev, add_comm] using hh
  have h := complex_monomial_difference_bound (p-1) p x y _ hR hx hy
  have h1 : p-1+p = 2*p-1 := by omega
  have h2 : p-1+p-1 = 2*p-2 := by omega
  simpa only [complexMomentTest,h1,h2] using h

end SpectralConsequences
