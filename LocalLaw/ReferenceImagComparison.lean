import LocalLaw.ReferenceBounds

/-!
# Comparing the physical reference imaginary parts

The rational tree transform controls Im(m) from below uniformly on the unit
disk. Thus bounds measured by Im(m) can be converted to the source Im(md)
normalization without a Stieltjes integral assumption.
-/

namespace LocalLaw

theorem rationalTreeReference_im (k : ℕ) (hk : 0 < k) (m : ℂ) :
    (rationalTreeReference k m).im =
      m.im * (1 + ‖m‖ ^ 2 / (k : ℝ)) / Complex.normSq (1 - m ^ 2 / (k : ℂ)) := by
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hk)
  have hn : ‖m‖ ^ 2 = m.re ^ 2 + m.im ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.sq_norm m
  unfold rationalTreeReference
  rw [Complex.div_im, ← sub_div]
  congr 1
  rw [hn]
  simp only [Complex.sub_re, Complex.one_re, Complex.div_re, Complex.sub_im,
    Complex.one_im, Complex.div_im, Complex.natCast_re, Complex.natCast_im,
    mul_zero, zero_mul, add_zero, sub_zero, Complex.normSq_natCast, pow_two,
    Complex.mul_re, Complex.mul_im]
  field_simp
  ring

/-- The imaginary part comparison holds on the entire physical unit disk. -/
theorem im_le_rationalTreeReference (k : ℕ) (hk : 2 ≤ k) (m : ℂ)
    (hm : ‖m‖ ≤ 1) (him : 0 ≤ m.im) :
    m.im ≤ (3 / 2 : ℝ) * (rationalTreeReference k m).im := by
  let x := ‖m‖ ^ 2 / (k : ℝ)
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxhalf : x ≤ 1 / 2 := by
    have hh := tree_correction_norm_le_half k hk m hm
    simpa only [norm_div, norm_pow, Complex.norm_natCast] using hh
  have hden := tree_reference_denominator_lower k hk m hm
  have hnorm : ‖1 - m ^ 2 / (k : ℂ)‖ ≤ 1 + x := by
    have hh := norm_sub_le (1 : ℂ) (m ^ 2 / (k : ℂ))
    simpa only [norm_one, norm_div, norm_pow, Complex.norm_natCast] using hh
  have hD : 0 < Complex.normSq (1 - m ^ 2 / (k : ℂ)) := by
    rw [← Complex.sq_norm]
    positivity
  have hDupper : Complex.normSq (1 - m ^ 2 / (k : ℂ)) ≤ (3 / 2 : ℝ) * (1 + x) := by
    have hh := pow_le_pow_left₀ (norm_nonneg (1 - m ^ 2 / (k : ℂ))) hnorm 2
    rw [Complex.sq_norm] at hh
    nlinarith
  rw [rationalTreeReference_im k (by omega) m, ← mul_div_assoc]
  apply (le_div_iff₀ hD).mpr
  have hh := mul_le_mul_of_nonneg_left hDupper him
  dsimp only [x] at hh
  nlinarith

/-- The source normalizations differ by at most the fixed factor 3/2. -/
theorem semicircleRoot_im_le_md (d : ℕ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) :
    (semicircleRoot z).im ≤ (3 / 2 : ℝ) * (kestenMcKayTransform d (semicircleRoot z) z).im := by
  rw [kestenMcKayTransform_eq d hd _ z (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le]
  exact im_le_rationalTreeReference (d - 1) (by omega) (semicircleRoot z)
    (semicircleRoot_norm_le_one z) (semicircleRoot_im_pos hz).le

end LocalLaw
