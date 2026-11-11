import Mathlib

/-!
# Elementary moduli for the local-law error parameters

The square root is globally one-half Hölder on nonnegative reals. Quotients
with positive denominators bounded below have an explicit variation bound.
These estimates keep the actual error-budget continuity separate from its
threshold inflation.
-/

namespace LocalLaw

theorem sqrt_holder_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| := by
  have hsa := Real.sqrt_nonneg a
  have hsb := Real.sqrt_nonneg b
  have hsqa := Real.sq_sqrt ha
  have hsqb := Real.sq_sqrt hb
  have hquad : (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
    by_cases hab : a ≤ b
    · have hroots := Real.sqrt_le_sqrt hab
      rw [abs_of_nonpos (sub_nonpos.mpr hab)]
      nlinarith [mul_le_mul_of_nonneg_left hroots hsa]
    · have hba : b ≤ a := le_of_not_ge hab
      have hroots := Real.sqrt_le_sqrt hba
      rw [abs_of_nonneg (sub_nonneg.mpr hba)]
      nlinarith [mul_le_mul_of_nonneg_left hroots hsb]
  have hsquare := Real.sq_sqrt (abs_nonneg (a - b))
  have habs : |Real.sqrt a - Real.sqrt b| ^ 2 = (Real.sqrt a - Real.sqrt b) ^ 2 := sq_abs _
  nlinarith [abs_nonneg (Real.sqrt a - Real.sqrt b), Real.sqrt_nonneg |a - b|]

/-- Real quotient continuity with explicit denominator, numerator, and
variation bounds. The final modulus is derived from the quotient identity. -/
theorem quotient_variation_bound (a b x y η M K D : ℝ)
    (hη : 0 < η) (hx : η ≤ x) (hy : η ≤ y)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hb : |b| ≤ M) (hab : |a - b| ≤ K * D) (hxy : |x - y| ≤ D) :
    |a / x - b / y| ≤ (K / η + M / η ^ 2) * D := by
  have hxp : 0 < x := hη.trans_le hx
  have hyp : 0 < y := hη.trans_le hy
  have hid : a / x - b / y = (a - b) / x + b * (y - x) / (x * y) := by
    field_simp
    ring
  have hden : η ^ 2 ≤ x * y := by nlinarith
  have hfirst : |a - b| / x ≤ (K * D) / η :=
    div_le_div₀ (mul_nonneg hK hD) hab hη hx
  have hnum : |b| * |y - x| ≤ M * D := by
    rw [abs_sub_comm] at hxy
    exact mul_le_mul hb hxy (abs_nonneg _) hM
  have hsecond : (|b| * |y - x|) / (x * y) ≤ (M * D) / η ^ 2 :=
    div_le_div₀ (mul_nonneg hM hD) hnum (sq_pos_of_pos hη) hden
  rw [hid]
  calc
    _ ≤ |(a - b) / x| + |b * (y - x) / (x * y)| := abs_add_le _ _
    _ = |a - b| / x + (|b| * |y - x|) / (x * y) := by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hxp, abs_of_pos (mul_pos hxp hyp)]
    _ ≤ (K * D) / η + (M * D) / η ^ 2 := add_le_add hfirst hsecond
    _ = (K / η + M / η ^ 2) * D := by ring

/-- Explicit Lipschitz modulus of the final fractional-power error term on
a positive half-line. -/
theorem inverse_two_thirds_lipschitz (η x y : ℝ) (hη : 0 < η)
    (hx : η ≤ x) (hy : η ≤ y) :
    |x ^ (- (2 / 3 : ℝ)) - y ^ (- (2 / 3 : ℝ))| ≤
      ((2 / 3 : ℝ) * η ^ (- (5 / 3 : ℝ))) * |x - y| := by
  have hderiv : ∀ u ∈ Set.Ici η,
      HasDerivWithinAt (fun t : ℝ => t ^ (- (2 / 3 : ℝ)))
        ((- (2 / 3 : ℝ)) * u ^ (- (5 / 3 : ℝ))) (Set.Ici η) u := by
    intro u hu
    have hup : 0 < u := hη.trans_le hu
    have hd := Real.hasDerivAt_rpow_const (p := - (2 / 3 : ℝ)) (Or.inl (ne_of_gt hup))
    have hp : (- (2 / 3 : ℝ)) - 1 = - (5 / 3 : ℝ) := by norm_num
    rw [hp] at hd
    exact hd.hasDerivWithinAt
  have hbound : ∀ u ∈ Set.Ici η,
      ‖(- (2 / 3 : ℝ)) * u ^ (- (5 / 3 : ℝ))‖ ≤
        ((2 / 3 : ℝ) * η ^ (- (5 / 3 : ℝ))) := by
    intro u hu
    have hup : 0 < u := hη.trans_le hu
    have hpow := Real.rpow_le_rpow_of_nonpos hη hu (by norm_num : - (5 / 3 : ℝ) ≤ 0)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hup.le _)]
    rw [abs_of_nonpos (by norm_num : -(2 / 3 : ℝ) ≤ 0)]
    simp only [neg_neg]
    exact mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_Ici η) hy hx
  simpa only [Real.norm_eq_abs] using h


end LocalLaw
