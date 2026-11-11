import Mathlib

/-!
# Exact scalar cavity recursion

A complete finite algebraic model for the cavity-tree recursion used in the
proof of Theorem 4.2. The graph-to-recursion identification is a separate input.
All inverses below have explicit nonvanishing hypotheses, proved automatically
from the small-displacement bound when the reference root has norm at most one.
-/

open scoped BigOperators

namespace LocalLaw

/-- The geometric sum controlling a depth-`n` cavity iteration. -/
noncomputable def cavitySum (m : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range n, m ^ (2 * j)

/-- The denominator in the exact fractional-linear formula. -/
noncomputable def cavityDenominator (m δ : ℂ) (n : ℕ) : ℂ :=
  1 - m * cavitySum m n * δ

/-- Iteration of the scalar cavity map, with zero iterations equal to the input.
A tree of radius `ℓ` corresponds to `ℓ + 1` iterations. -/
noncomputable def cavityIterate (z w : ℂ) : ℕ → ℂ
  | 0 => w
  | n + 1 => -(z + cavityIterate z w n)⁻¹

@[simp] theorem cavitySum_zero (m : ℂ) : cavitySum m 0 = 0 := by
  simp [cavitySum]

@[simp] theorem cavitySum_succ (m : ℂ) (n : ℕ) :
    cavitySum m (n + 1) = cavitySum m n + m ^ (2 * n) := by
  simp [cavitySum, Finset.sum_range_succ]

@[simp] theorem cavityDenominator_zero (m δ : ℂ) :
    cavityDenominator m δ 0 = 1 := by
  simp [cavityDenominator]

theorem cavitySum_shift (m : ℂ) (n : ℕ) :
    cavitySum m (n + 1) = 1 + m ^ 2 * cavitySum m n := by
  unfold cavitySum
  rw [Finset.sum_range_succ']
  simp only [Nat.mul_zero, pow_zero]
  rw [Finset.mul_sum, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
  ring

theorem cavitySum_geometric (m : ℂ) (n : ℕ) :
    (1 - m ^ 2) * cavitySum m n = 1 - m ^ (2 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [cavitySum_succ, mul_add, ih]
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
      ring

theorem cavity_root_ne_zero {m z : ℂ} (hm : m ^ 2 + z * m + 1 = 0) : m ≠ 0 := by
  intro hzero
  simp [hzero] at hm

/-- The exact iteration, assuming all of its closed-form denominators are
nonzero. The hypotheses also imply that every recursive inverse is legitimate. -/
theorem cavity_iterate_exact {m z w : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) (n : ℕ)
    (hden : ∀ k ≤ n, cavityDenominator m (w - m) k ≠ 0) :
    cavityIterate z w n =
      m + m ^ (2 * n) * (w - m) / cavityDenominator m (w - m) n := by
  have hm0 : m ≠ 0 := cavity_root_ne_zero hm
  induction n with
  | zero => simp [cavityIterate]
  | succ n ih =>
      have hdn := hden n (Nat.le_succ n)
      have hdsn := hden (n + 1) le_rfl
      have ih' := ih (fun k hk => hden k (Nat.le_trans hk (Nat.le_succ n)))
      have hstep : z + cavityIterate z w n =
          -cavityDenominator m (w - m) (n + 1) /
            (m * cavityDenominator m (w - m) n) := by
        rw [ih']
        apply (eq_div_iff (mul_ne_zero hm0 hdn)).2
        field_simp [hdn]
        dsimp [cavityDenominator]
        rw [cavitySum_succ]
        linear_combination (1 - m * cavitySum m n * (w - m)) ^ 2 * hm
      rw [cavityIterate, hstep]
      have hpow : m ^ (2 * (n + 1)) = m ^ (2 * n) * m ^ 2 := by
        rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
      simp only [neg_div, inv_neg, neg_neg, inv_div]
      rw [hpow]
      apply (div_eq_iff hdsn).2
      field_simp [hdsn]
      dsimp [cavityDenominator]
      rw [cavitySum_succ]
      ring

/-- Exact conversion of a finite-iteration residual to the semicircle
quadratic residual. There is no Taylor or cubic remainder. -/
theorem cavity_residual_identity {m z w : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) (n : ℕ)
    (hden : ∀ k ≤ n, cavityDenominator m (w - m) k ≠ 0) :
    cavityDenominator m (w - m) n * (w - cavityIterate z w n) =
      -(m * cavitySum m n) * (w ^ 2 + z * w + 1) := by
  rw [cavity_iterate_exact hm n hden]
  have hdn := hden n le_rfl
  field_simp [hdn]
  dsimp [cavityDenominator]
  have hgeom := cavitySum_geometric m n
  linear_combination -(w - m) * hgeom + cavitySum m n * w * hm

/-- The geometric sum has at most one unit of norm per summand. -/
theorem cavitySum_norm_le {m : ℂ} (hm : ‖m‖ ≤ 1) (n : ℕ) :
    ‖cavitySum m n‖ ≤ (n : ℝ) := by
  calc
    ‖cavitySum m n‖ ≤ ∑ j ∈ Finset.range n, ‖m ^ (2 * j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg m) hm
    _ = (n : ℝ) := by simp

/-- Small displacements bound the exact denominator away from zero. -/
theorem cavityDenominator_bounds {m δ : ℂ} (hm : ‖m‖ ≤ 1) (n : ℕ)
    (hsmall : (n : ℝ) * ‖δ‖ ≤ 1 / 2) :
    1 / 2 ≤ ‖cavityDenominator m δ n‖ ∧
      ‖cavityDenominator m δ n‖ ≤ 3 / 2 := by
  have hprod : ‖m * cavitySum m n * δ‖ ≤ 1 / 2 := by
    calc
      ‖m * cavitySum m n * δ‖ = ‖m‖ * ‖cavitySum m n‖ * ‖δ‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ 1 * (n : ℝ) * ‖δ‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hm (cavitySum_norm_le hm n) (norm_nonneg _) (by norm_num))
          (norm_nonneg _)
      _ ≤ 1 / 2 := by simpa using hsmall
  have hlow := norm_sub_norm_le (1 : ℂ) (m * cavitySum m n * δ)
  have hupp := norm_sub_le (1 : ℂ) (m * cavitySum m n * δ)
  simp only [norm_one] at hlow hupp
  change 1 / 2 ≤ ‖1 - m * cavitySum m n * δ‖ ∧
    ‖1 - m * cavitySum m n * δ‖ ≤ 3 / 2
  constructor <;> linarith

theorem cavityDenominator_ne_zero {m δ : ℂ} (hm : ‖m‖ ≤ 1) (n : ℕ)
    (hsmall : (n : ℝ) * ‖δ‖ ≤ 1 / 2) :
    cavityDenominator m δ n ≠ 0 := by
  apply norm_pos_iff.mp
  have hb := (cavityDenominator_bounds hm n hsmall).1
  linarith

/-- The small-displacement condition at the last depth validates every earlier
closed-form denominator. -/
theorem cavityDenominator_all_ne_zero {m δ : ℂ} (hm : ‖m‖ ≤ 1) (n : ℕ)
    (hsmall : (n : ℝ) * ‖δ‖ ≤ 1 / 2) :
    ∀ k ≤ n, cavityDenominator m δ k ≠ 0 := by
  intro k hk
  apply cavityDenominator_ne_zero hm k
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) (norm_nonneg δ)).trans hsmall

/-- Exact cavity iteration with the analytic denominator hypotheses discharged
by one explicit smallness condition. -/
theorem cavity_iterate_exact_of_small {m z w : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) (hmnorm : ‖m‖ ≤ 1) (n : ℕ)
    (hsmall : (n : ℝ) * ‖w - m‖ ≤ 1 / 2) :
    cavityIterate z w n =
      m + m ^ (2 * n) * (w - m) / cavityDenominator m (w - m) n :=
  cavity_iterate_exact hm n (cavityDenominator_all_ne_zero hmnorm n hsmall)

theorem cavity_residual_identity_of_small {m z w : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) (hmnorm : ‖m‖ ≤ 1) (n : ℕ)
    (hsmall : (n : ℝ) * ‖w - m‖ ≤ 1 / 2) :
    cavityDenominator m (w - m) n * (w - cavityIterate z w n) =
      -(m * cavitySum m n) * (w ^ 2 + z * w + 1) :=
  cavity_residual_identity hm n (cavityDenominator_all_ne_zero hmnorm n hsmall)

/-- At least one of any two adjacent depths is nonresonant. -/
theorem cavitySum_adjacent_nonresonance {m : ℂ} (hm : ‖m‖ ≤ 1) (n : ℕ) :
    1 / 2 ≤ ‖cavitySum m n‖ ∨ 1 / 2 ≤ ‖cavitySum m (n + 1)‖ := by
  have hid : cavitySum m (n + 1) - m ^ 2 * cavitySum m n = 1 := by
    rw [cavitySum_shift]
    ring
  have htri := norm_sub_le (cavitySum m (n + 1)) (m ^ 2 * cavitySum m n)
  rw [hid, norm_one, norm_mul, norm_pow] at htri
  have hp : ‖m‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hm
  have hmul : ‖m‖ ^ 2 * ‖cavitySum m n‖ ≤ ‖cavitySum m n‖ := by
    simpa using mul_le_mul_of_nonneg_right hp (norm_nonneg (cavitySum m n))
  by_cases hn : 1 / 2 ≤ ‖cavitySum m n‖
  · exact Or.inl hn
  · right
    linarith

/-- The reference root and its reciprocal are the two roots of the quadratic. -/
theorem cavity_quadratic_factor {m z w : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) :
    w ^ 2 + z * w + 1 = (w - m) * ((w - m) - (m⁻¹ - m)) := by
  have hm0 := cavity_root_ne_zero hm
  field_simp [hm0]
  linear_combination w * hm

/-- Norm conversion of the exact residual. This version exposes the lower
bound on the nonresonant coefficient as a separate input. -/
theorem cavity_polynomial_residual_bound {m z w : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) (hmnorm : ‖m‖ ≤ 1) (n : ℕ)
    (hsmall : (n : ℝ) * ‖w - m‖ ≤ 1 / 2)
    {c : ℝ} (hc : 0 < c) (hcoeff : c ≤ ‖m * cavitySum m n‖) :
    ‖w ^ 2 + z * w + 1‖ ≤
      (3 / 2) / c * ‖w - cavityIterate z w n‖ := by
  have hid := congrArg norm (cavity_residual_identity_of_small hm hmnorm n hsmall)
  simp only [norm_mul, norm_neg] at hid
  have hd := (cavityDenominator_bounds hmnorm n hsmall).2
  have hres : c * ‖w ^ 2 + z * w + 1‖ ≤
      (3 / 2) * ‖w - cavityIterate z w n‖ := by
    calc
      c * ‖w ^ 2 + z * w + 1‖ ≤
          ‖m‖ * ‖cavitySum m n‖ * ‖w ^ 2 + z * w + 1‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [norm_mul] using hcoeff
      _ = ‖cavityDenominator m (w - m) n‖ *
          ‖w - cavityIterate z w n‖ := hid.symm
      _ ≤ (3 / 2) * ‖w - cavityIterate z w n‖ :=
        mul_le_mul_of_nonneg_right hd (norm_nonneg _)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).2
  nlinarith [hres]

/-- The recursive inverse denominator is a ratio of consecutive exact
closed-form denominators. This cross-multiplied form needs no inverse at the
next step. -/
theorem cavity_iterate_denominator_relation {m z w : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) (n : ℕ)
    (hden : ∀ k ≤ n, cavityDenominator m (w - m) k ≠ 0) :
    (z + cavityIterate z w n) * (m * cavityDenominator m (w - m) n) =
      -cavityDenominator m (w - m) (n + 1) := by
  rw [cavity_iterate_exact hm n hden]
  have hdn := hden n le_rfl
  field_simp [hdn]
  dsimp [cavityDenominator]
  rw [cavitySum_succ]
  linear_combination (1 - m * cavitySum m n * (w - m)) ^ 2 * hm

/-- Every inverse in the recursive cavity map is legitimate when the
corresponding closed-form denominators are nonzero. -/
theorem cavity_iterate_step_ne_zero {m z w : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) (n : ℕ)
    (hden : ∀ k ≤ n + 1, cavityDenominator m (w - m) k ≠ 0) :
    z + cavityIterate z w n ≠ 0 := by
  have hid := cavity_iterate_denominator_relation hm n
    (fun k hk => hden k (Nat.le_trans hk (Nat.le_succ n)))
  intro hzero
  rw [hzero, zero_mul] at hid
  exact hden (n + 1) le_rfl (neg_eq_zero.mp hid.symm)

theorem cavity_iterate_step_ne_zero_of_small {m z w : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) (hmnorm : ‖m‖ ≤ 1) (n : ℕ)
    (hsmall : ((n + 1 : ℕ) : ℝ) * ‖w - m‖ ≤ 1 / 2) :
    z + cavityIterate z w n ≠ 0 :=
  cavity_iterate_step_ne_zero hm n (cavityDenominator_all_ne_zero hmnorm (n + 1) hsmall)

/-- On a bounded spectral region the physical root cannot have arbitrarily
small norm. The upper norm bound selects the relevant quantitative scale. -/
theorem cavity_root_norm_lower_bound {m z : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) (hmnorm : ‖m‖ ≤ 1)
    {B : ℝ} (hz : ‖z‖ ≤ B) :
    1 / (B + 1) ≤ ‖m‖ := by
  have hB : 0 ≤ B := (norm_nonneg z).trans hz
  have hBpos : 0 < B + 1 := by linarith
  have hid : m * (z + m) = -(1 : ℂ) := by linear_combination hm
  have hnorm : (1 : ℝ) = ‖m‖ * ‖z + m‖ := by
    rw [← norm_mul, hid, norm_neg, norm_one]
  apply (div_le_iff₀ hBpos).2
  calc
    1 = ‖m‖ * ‖z + m‖ := hnorm
    _ ≤ ‖m‖ * (‖z‖ + ‖m‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ ‖m‖ * (B + 1) :=
      mul_le_mul_of_nonneg_left (add_le_add hz hmnorm) (norm_nonneg _)

/-- The separation between the two quadratic roots has the expected algebraic
square, before any estimates on a spectral domain are made. -/
theorem cavity_root_gap_sq {m z : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) :
    (m⁻¹ - m) ^ 2 = z ^ 2 - 4 := by
  have hm0 := cavity_root_ne_zero hm
  have hz : z = -(m + m⁻¹) := by
    field_simp [hm0]
    linear_combination hm
  rw [hz]
  field_simp [hm0]
  ring

/-- An explicit bounded-spectral-domain conversion with the coefficient
`3 * (B + 1)` used in the mathematical blueprint. -/
theorem cavity_polynomial_residual_bound_bounded {m z w : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) (hmnorm : ‖m‖ ≤ 1) (n : ℕ)
    (hsmall : (n : ℝ) * ‖w - m‖ ≤ 1 / 2)
    (hnonresonant : 1 / 2 ≤ ‖cavitySum m n‖)
    {B : ℝ} (hz : ‖z‖ ≤ B) :
    ‖w ^ 2 + z * w + 1‖ ≤
      (3 * (B + 1)) * ‖w - cavityIterate z w n‖ := by
  have hB : 0 ≤ B := (norm_nonneg z).trans hz
  have hBpos : 0 < B + 1 := by linarith
  have hc : (0 : ℝ) < 1 / (2 * (B + 1)) := by positivity
  have hcoeff : 1 / (2 * (B + 1)) ≤ ‖m * cavitySum m n‖ := by
    rw [norm_mul]
    calc
      1 / (2 * (B + 1)) = (1 / (B + 1)) * (1 / 2) := by
        field_simp
        ring
      _ ≤ ‖m‖ * ‖cavitySum m n‖ :=
        mul_le_mul (cavity_root_norm_lower_bound hm hmnorm hz) hnonresonant
          (by norm_num) (norm_nonneg _)
  have hbound := cavity_polynomial_residual_bound hm hmnorm n hsmall hc hcoeff
  have hconst : (3 / 2 : ℝ) / (1 / (2 * (B + 1))) = 3 * (B + 1) := by
    field_simp
    ring
  simpa only [hconst] using hbound

end LocalLaw
