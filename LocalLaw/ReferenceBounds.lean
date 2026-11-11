import LocalLaw.RegularTree
import LocalLaw.Semicircle

/-!
# Uniform regular-tree transform bounds

For d≥3 the rational Kesten--McKay transform has denominator bounded below
by 1/2 on the closed unit disk. Its norm is at most 2 and its Lipschitz
constant in the cavity root is at most 6. Together with the physical root
continuity this gives an explicit spectral modulus without a Stieltjes integral.
-/

namespace LocalLaw

noncomputable def rationalTreeReference (k : ℕ) (m : ℂ) : ℂ :=
  m / (1 - m ^ 2 / (k : ℂ))

theorem tree_correction_norm_le_half (k : ℕ) (hk : 2 ≤ k) (m : ℂ) (hm : ‖m‖ ≤ 1) :
    ‖m ^ 2 / (k : ℂ)‖ ≤ 1 / 2 := by
  have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  calc
    ‖m ^ 2 / (k : ℂ)‖ = ‖m‖ ^ 2 / (k : ℝ) := by simp
    _ ≤ 1 / (k : ℝ) := div_le_div_of_nonneg_right (pow_le_one₀ (norm_nonneg m) hm) hkp.le
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hk2

theorem tree_reference_denominator_lower (k : ℕ) (hk : 2 ≤ k) (m : ℂ) (hm : ‖m‖ ≤ 1) :
    1 / 2 ≤ ‖1 - m ^ 2 / (k : ℂ)‖ := by
  have ht := tree_correction_norm_le_half k hk m hm
  have hnorm := norm_sub_norm_le (1 : ℂ) (m ^ 2 / (k : ℂ))
  simp only [norm_one] at hnorm
  linarith

theorem rationalTreeReference_norm_le_two (k : ℕ) (hk : 2 ≤ k) (m : ℂ) (hm : ‖m‖ ≤ 1) :
    ‖rationalTreeReference k m‖ ≤ 2 := by
  have hd := tree_reference_denominator_lower k hk m hm
  have hdp : 0 < ‖1 - m ^ 2 / (k : ℂ)‖ := by linarith
  unfold rationalTreeReference
  rw [norm_div]
  apply (div_le_iff₀ hdp).mpr
  linarith

/-- Exact rational difference, with both denominator hypotheses explicit. -/
theorem rationalTreeReference_sub (k : ℕ) (a b : ℂ)
    (ha : 1 - a ^ 2 / (k : ℂ) ≠ 0) (hb : 1 - b ^ 2 / (k : ℂ) ≠ 0) :
    rationalTreeReference k a - rationalTreeReference k b =
      (a - b) * (1 + a * b / (k : ℂ)) /
        ((1 - a ^ 2 / (k : ℂ)) * (1 - b ^ 2 / (k : ℂ))) := by
  unfold rationalTreeReference
  rw [div_sub_div a b ha hb]
  congr 1
  ring

theorem rationalTreeReference_lipschitz (k : ℕ) (hk : 2 ≤ k) (a b : ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖rationalTreeReference k a - rationalTreeReference k b‖ ≤ 6 * ‖a - b‖ := by
  have hda := tree_reference_denominator_lower k hk a ha
  have hdb := tree_reference_denominator_lower k hk b hb
  have hdap : 0 < ‖1 - a ^ 2 / (k : ℂ)‖ := by linarith
  have hdbp : 0 < ‖1 - b ^ 2 / (k : ℂ)‖ := by linarith
  have hda0 : 1 - a ^ 2 / (k : ℂ) ≠ 0 := norm_pos_iff.mp hdap
  have hdb0 : 1 - b ^ 2 / (k : ℂ) ≠ 0 := norm_pos_iff.mp hdbp
  have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hprod : ‖a * b / (k : ℂ)‖ ≤ 1 / 2 := by
    calc
      _ = (‖a‖ * ‖b‖) / (k : ℝ) := by simp
      _ ≤ 1 / (k : ℝ) := by
        apply div_le_div_of_nonneg_right _ hkp.le
        nlinarith [norm_nonneg a, norm_nonneg b]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hk2
  have hnum : ‖1 + a * b / (k : ℂ)‖ ≤ 3 / 2 := by
    have := norm_add_le (1 : ℂ) (a * b / (k : ℂ))
    simp only [norm_one] at this
    linarith
  have hden : 1 / 4 ≤ ‖1 - a ^ 2 / (k : ℂ)‖ * ‖1 - b ^ 2 / (k : ℂ)‖ := by
    nlinarith
  rw [rationalTreeReference_sub k a b hda0 hdb0, norm_div, norm_mul, norm_mul]
  apply (div_le_iff₀ (mul_pos hdap hdbp)).mpr
  have hleft := mul_le_mul_of_nonneg_left hnum (norm_nonneg (a - b))
  have hright := mul_le_mul_of_nonneg_left hden (show 0 ≤ 6 * ‖a - b‖ by positivity)
  nlinarith

theorem kestenMcKayTransform_norm_le_two (d : ℕ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) :
    ‖kestenMcKayTransform d (semicircleRoot z) z‖ ≤ 2 := by
  rw [kestenMcKayTransform_eq d hd _ z (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le]
  exact rationalTreeReference_norm_le_two (d - 1) (by omega) _ (semicircleRoot_norm_le_one z)

/-- The reference spectral modulus needed by the paper error parameters. -/
theorem kestenMcKayTransform_lipschitz (d : ℕ) (hd : 3 ≤ d) (z w : ℂ)
    (η₀ : ℝ) (hη : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im) :
    ‖kestenMcKayTransform d (semicircleRoot z) z -
      kestenMcKayTransform d (semicircleRoot w) w‖ ≤ (6 / η₀) * dist z w := by
  have hzp : 0 < z.im := hη.trans_le hz
  have hwp : 0 < w.im := hη.trans_le hw
  rw [kestenMcKayTransform_eq d hd _ z (semicircleRoot_equation z) hzp
      (semicircleRoot_im_pos hzp).le,
    kestenMcKayTransform_eq d hd _ w (semicircleRoot_equation w) hwp
      (semicircleRoot_im_pos hwp).le]
  have hr := rationalTreeReference_lipschitz (d - 1) (by omega)
    (semicircleRoot z) (semicircleRoot w) (semicircleRoot_norm_le_one z) (semicircleRoot_norm_le_one w)
  have hm := semicircleRoot_lipschitz (z := z) (w := w) η₀ hη hz hw
  calc
    _ ≤ 6 * ‖semicircleRoot z - semicircleRoot w‖ := hr
    _ ≤ 6 * (‖z - w‖ / η₀) := mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = (6 / η₀) * dist z w := by rw [dist_eq_norm]; ring

end LocalLaw
