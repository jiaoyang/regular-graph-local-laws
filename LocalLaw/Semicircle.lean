import LocalLaw.ScalarRecursion

/-!
# The physical algebraic semicircle root

The unique small root of m²+zm+1=0 is constructed from algebraic closure of
C. On the upper half-plane it has norm strictly below one and positive
imaginary part. This module does not assert the Stieltjes integral formula.
-/

namespace LocalLaw

/-- An auxiliary algebraic square root. The eventual physical root is unique,
so on the upper half-plane it does not depend on this auxiliary choice. -/
noncomputable def algebraicComplexSqrt (z : ℂ) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq z (n := 2) (by norm_num))

theorem algebraicComplexSqrt_sq (z : ℂ) : algebraicComplexSqrt z ^ 2 = z :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq z (n := 2) (by norm_num))

noncomputable def quadraticRootPlus (z : ℂ) : ℂ :=
  (-z + algebraicComplexSqrt (z ^ 2 - 4)) / 2

noncomputable def quadraticRootMinus (z : ℂ) : ℂ :=
  (-z - algebraicComplexSqrt (z ^ 2 - 4)) / 2

theorem quadraticRootPlus_equation (z : ℂ) :
    quadraticRootPlus z ^ 2 + z * quadraticRootPlus z + 1 = 0 := by
  unfold quadraticRootPlus
  linear_combination (1 / 4 : ℂ) * algebraicComplexSqrt_sq (z ^ 2 - 4)

theorem quadraticRootMinus_equation (z : ℂ) :
    quadraticRootMinus z ^ 2 + z * quadraticRootMinus z + 1 = 0 := by
  unfold quadraticRootMinus
  linear_combination (1 / 4 : ℂ) * algebraicComplexSqrt_sq (z ^ 2 - 4)

theorem quadraticRoots_product (z : ℂ) :
    quadraticRootPlus z * quadraticRootMinus z = 1 := by
  unfold quadraticRootPlus quadraticRootMinus
  linear_combination -(1 / 4 : ℂ) * algebraicComplexSqrt_sq (z ^ 2 - 4)

/-- Select a root of norm at most one. This total algebraic definition is used
only with the appropriate spectral-domain hypotheses in analytic theorems. -/
noncomputable def semicircleRoot (z : ℂ) : ℂ :=
  if ‖quadraticRootPlus z‖ ≤ 1 then quadraticRootPlus z else quadraticRootMinus z

theorem semicircleRoot_equation (z : ℂ) :
    semicircleRoot z ^ 2 + z * semicircleRoot z + 1 = 0 := by
  unfold semicircleRoot
  split
  · exact quadraticRootPlus_equation z
  · exact quadraticRootMinus_equation z

theorem semicircleRoot_norm_le_one (z : ℂ) : ‖semicircleRoot z‖ ≤ 1 := by
  unfold semicircleRoot
  split
  next h => exact h
  next h =>
    have hp : ‖quadraticRootPlus z‖ * ‖quadraticRootMinus z‖ = 1 := by
      simpa only [norm_mul, norm_one] using congrArg norm (quadraticRoots_product z)
    have ha : 1 < ‖quadraticRootPlus z‖ := lt_of_not_ge h
    by_contra hb
    have hb' : 1 < ‖quadraticRootMinus z‖ := lt_of_not_ge hb
    have hmul := mul_lt_mul_of_pos_left hb' (show 0 < ‖quadraticRootPlus z‖ by linarith)
    nlinarith

/-- The polynomial equation gives the characteristic imaginary-part identity. -/
theorem cavity_root_imaginary_identity {m z : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) :
    z.im * ‖m‖ ^ 2 = m.im * (1 - ‖m‖ ^ 2) := by
  have hnorm : m * star m = (‖m‖ ^ 2 : ℝ) := by
    simpa only [Complex.normSq_eq_norm_sq] using Complex.mul_conj m
  have hmult : (m + z) * (‖m‖ ^ 2 : ℝ) + star m = 0 := by
    calc
      (m + z) * (‖m‖ ^ 2 : ℝ) + star m =
          (m ^ 2 + z * m + 1) * star m := by rw [← hnorm]; ring
      _ = 0 := by rw [hm]; simp
  have him := congrArg Complex.im hmult
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im,
    Complex.ofReal_re, mul_zero, zero_add, Complex.star_def, Complex.conj_im,
    Complex.zero_im] at him
  nlinarith

/-- A small root at an upper-half-plane parameter lies strictly inside the
unit disk and has positive imaginary part. -/
theorem physical_cavity_root {m z : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hnorm : ‖m‖ ≤ 1) :
    ‖m‖ < 1 ∧ 0 < m.im := by
  have hid := cavity_root_imaginary_identity hm
  have hm0 : m ≠ 0 := cavity_root_ne_zero hm
  have hnormpos : 0 < ‖m‖ := norm_pos_iff.mpr hm0
  have hstrict : ‖m‖ < 1 := by
    by_contra h
    have heq : ‖m‖ = 1 := le_antisymm hnorm (le_of_not_gt h)
    rw [heq] at hid
    norm_num at hid
    linarith
  have hfactor : 0 < 1 - ‖m‖ ^ 2 := by nlinarith [norm_nonneg m]
  refine ⟨hstrict, ?_⟩
  by_contra h
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hfactor.le
  have hpositive : 0 < z.im * ‖m‖ ^ 2 := by positivity
  linarith

theorem semicircleRoot_physical {z : ℂ} (hz : 0 < z.im) :
    ‖semicircleRoot z‖ < 1 ∧ 0 < (semicircleRoot z).im :=
  physical_cavity_root (semicircleRoot_equation z) hz (semicircleRoot_norm_le_one z)

theorem semicircleRoot_norm_lt_one {z : ℂ} (hz : 0 < z.im) :
    ‖semicircleRoot z‖ < 1 := (semicircleRoot_physical hz).1

theorem semicircleRoot_im_pos {z : ℂ} (hz : 0 < z.im) :
    0 < (semicircleRoot z).im := (semicircleRoot_physical hz).2

theorem semicircleRoot_ne_zero (z : ℂ) : semicircleRoot z ≠ 0 :=
  cavity_root_ne_zero (semicircleRoot_equation z)

/-- The upper-half-plane quadratic has exactly one root in the closed unit
disk; the boundary case has already been excluded by the imaginary identity. -/
theorem physical_cavity_root_unique {a b z : ℂ}
    (ha : a ^ 2 + z * a + 1 = 0) (hb : b ^ 2 + z * b + 1 = 0)
    (hz : 0 < z.im) (hanorm : ‖a‖ ≤ 1) (hbnorm : ‖b‖ ≤ 1) : a = b := by
  by_contra hne
  have hfactor : (a - b) * (a + b + z) = 0 := by
    linear_combination ha - hb
  have hsum : a + b + z = 0 := (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne)
  have hproduct : a * b = 1 := by linear_combination a * hsum - ha
  have hproductnorm : ‖a‖ * ‖b‖ = 1 := by
    simpa only [norm_mul, norm_one] using congrArg norm hproduct
  have hanorm' := (physical_cavity_root ha hz hanorm).1
  have hbnorm' := (physical_cavity_root hb hz hbnorm).1
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr (cavity_root_ne_zero ha)
  have hmul := mul_lt_mul_of_pos_left hbnorm' hapos
  nlinarith

theorem semicircleRoot_unique {m z : ℂ} (hz : 0 < z.im)
    (hm : m ^ 2 + z * m + 1 = 0) (hnorm : ‖m‖ ≤ 1) : m = semicircleRoot z :=
  physical_cavity_root_unique hm (semicircleRoot_equation z) hz hnorm
    (semicircleRoot_norm_le_one z)


/-- Imaginary positivity also gives a quantitative distance from the unit
circle, without any integral representation. -/
theorem physical_cavity_root_disk_gap {m z : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hnorm : ‖m‖ ≤ 1) :
    z.im * ‖m‖ ≤ 1 - ‖m‖ ^ 2 := by
  have hstrict := (physical_cavity_root hm hz hnorm).1
  have hpos : 0 < ‖m‖ := norm_pos_iff.mpr (cavity_root_ne_zero hm)
  have hfactor : 0 ≤ 1 - ‖m‖ ^ 2 := by nlinarith [norm_nonneg m]
  have him : m.im ≤ ‖m‖ := (le_abs_self m.im).trans (Complex.abs_im_le_norm m)
  have hbound := mul_le_mul_of_nonneg_right him hfactor
  rw [← cavity_root_imaginary_identity hm] at hbound
  have hmul : ‖m‖ * (z.im * ‖m‖) ≤ ‖m‖ * (1 - ‖m‖ ^ 2) := by
    nlinarith
  exact (mul_le_mul_left hpos).mp hmul

/-- Exact difference identity for the physical branch, valid for any roots
of the two corresponding quadratic equations. -/
theorem cavity_root_difference_identity {a b z w : ℂ}
    (ha : a ^ 2 + z * a + 1 = 0) (hb : b ^ 2 + w * b + 1 = 0) :
    (a - b) * (1 - a * b) = (z - w) * a * b := by
  linear_combination -b * ha + a * hb

/-- Root continuity on a positive-imaginary-part domain, proved directly from
the quadratic equation and the physical-branch norm bounds. -/
theorem physical_cavity_root_lipschitz {a b z w : ℂ} (η₀ : ℝ)
    (hη₀ : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im)
    (ha : a ^ 2 + z * a + 1 = 0) (hb : b ^ 2 + w * b + 1 = 0)
    (hanorm : ‖a‖ ≤ 1) (hbnorm : ‖b‖ ≤ 1) :
    ‖a - b‖ ≤ ‖z - w‖ / η₀ := by
  have hzp : 0 < z.im := hη₀.trans_le hz
  have hwp : 0 < w.im := hη₀.trans_le hw
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr (cavity_root_ne_zero ha)
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr (cavity_root_ne_zero hb)
  have hga : η₀ * ‖a‖ ≤ 1 - ‖a‖ ^ 2 :=
    (mul_le_mul_of_nonneg_right hz (norm_nonneg a)).trans
      (physical_cavity_root_disk_gap ha hzp hanorm)
  have hgb : η₀ * ‖b‖ ≤ 1 - ‖b‖ ^ 2 :=
    (mul_le_mul_of_nonneg_right hw (norm_nonneg b)).trans
      (physical_cavity_root_disk_gap hb hwp hbnorm)
  have hprod : 2 * (‖a‖ * ‖b‖) ≤ ‖a‖ + ‖b‖ := by
    have h₁ := mul_le_mul_of_nonneg_left hbnorm (norm_nonneg a)
    have h₂ := mul_le_mul_of_nonneg_left hanorm (norm_nonneg b)
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hprod hη₀.le
  have hgap : η₀ * (‖a‖ * ‖b‖) ≤ 1 - ‖a‖ * ‖b‖ := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have hreverse := norm_sub_norm_le (1 : ℂ) (a * b)
  simp only [norm_one, norm_mul] at hreverse
  have hdenominator : η₀ * (‖a‖ * ‖b‖) ≤ ‖1 - a * b‖ := hgap.trans hreverse
  have hid := congrArg norm (cavity_root_difference_identity ha hb)
  simp only [norm_mul] at hid
  have hmul : (‖a - b‖ * η₀) * (‖a‖ * ‖b‖) ≤
      ‖z - w‖ * (‖a‖ * ‖b‖) := by
    calc
      (‖a - b‖ * η₀) * (‖a‖ * ‖b‖)
          = ‖a - b‖ * (η₀ * (‖a‖ * ‖b‖)) := by ring
      _ ≤ ‖a - b‖ * ‖1 - a * b‖ :=
        mul_le_mul_of_nonneg_left hdenominator (norm_nonneg _)
      _ = ‖z - w‖ * (‖a‖ * ‖b‖) := by nlinarith [hid]
  have hcancel : ‖a - b‖ * η₀ ≤ ‖z - w‖ :=
    (mul_le_mul_right (mul_pos hapos hbpos)).mp hmul
  exact (le_div_iff₀ hη₀).2 hcancel

/-- The constructed semicircle reference has the spectral continuity required
by the generic net-transport lemmas. -/
theorem semicircleRoot_lipschitz {z w : ℂ} (η₀ : ℝ) (hη₀ : 0 < η₀)
    (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im) :
    ‖semicircleRoot z - semicircleRoot w‖ ≤ ‖z - w‖ / η₀ :=
  physical_cavity_root_lipschitz η₀ hη₀ hz hw (semicircleRoot_equation z)
    (semicircleRoot_equation w) (semicircleRoot_norm_le_one z) (semicircleRoot_norm_le_one w)

end LocalLaw
