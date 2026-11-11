import LocalLaw.ReferenceBounds
import LocalLaw.RealModulus
import LocalLaw.GraphTheorem42

/-!
# Quantitative continuity of the uninflated paper error

The regular-tree transform is bounded by two and has an explicit spectral
modulus. Quotient, square-root, and negative-power estimates give a concrete
modulus for all three terms of epsilon0. Threshold inflation is handled
separately by the branch-preserving net.
-/

namespace LocalLaw

theorem reference_variance_lipschitz (d : ℕ) (hd : 3 ≤ d) (z w : ℂ)
    (η₀ : ℝ) (hη : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im) :
    |(graphKestenMcKayReference d z).im / z.im -
      (graphKestenMcKayReference d w).im / w.im| ≤ (8 / η₀ ^ 2) * dist z w := by
  have hzp := hη.trans_le hz
  have hwp := hη.trans_le hw
  have hnorm := kestenMcKayTransform_norm_le_two d hd w hwp
  have hb : |(graphKestenMcKayReference d w).im| ≤ 2 :=
    (Complex.abs_im_le_norm _).trans hnorm
  have hdiff : |(graphKestenMcKayReference d z).im - (graphKestenMcKayReference d w).im| ≤
      (6 / η₀) * dist z w := by
    have hi := Complex.abs_im_le_norm (graphKestenMcKayReference d z - graphKestenMcKayReference d w)
    simp only [Complex.sub_im] at hi
    exact hi.trans (kestenMcKayTransform_lipschitz d hd z w η₀ hη hz hw)
  have hηdiff : |z.im - w.im| ≤ dist z w := by
    simpa only [dist_eq_norm, Complex.sub_im] using Complex.abs_im_le_norm (z - w)
  have h := quotient_variation_bound (graphKestenMcKayReference d z).im
    (graphKestenMcKayReference d w).im z.im w.im η₀ 2 (6 / η₀) (dist z w)
    hη hz hw (by norm_num) (by positivity) (dist_nonneg) hb hdiff hηdiff
  convert h using 1
  ring

theorem normalized_reference_variance_lipschitz (d N : ℕ) (hd : 3 ≤ d) (hN : 0 < N)
    (z w : ℂ) (η₀ : ℝ) (hη : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im) :
    |(graphKestenMcKayReference d z).im / ((N : ℝ) * z.im) -
      (graphKestenMcKayReference d w).im / ((N : ℝ) * w.im)| ≤
      (8 / ((N : ℝ) * η₀ ^ 2)) * dist z w := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hzp := hη.trans_le hz
  have hwp := hη.trans_le hw
  have hid : (graphKestenMcKayReference d z).im / ((N : ℝ) * z.im) -
      (graphKestenMcKayReference d w).im / ((N : ℝ) * w.im) =
      ((graphKestenMcKayReference d z).im / z.im -
       (graphKestenMcKayReference d w).im / w.im) / (N : ℝ) := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hNp]
  calc
    _ ≤ ((8 / η₀ ^ 2) * dist z w) / (N : ℝ) :=
      div_le_div_of_nonneg_right (reference_variance_lipschitz d hd z w η₀ hη hz hw) hNp.le
    _ = (8 / ((N : ℝ) * η₀ ^ 2)) * dist z w := by ring

theorem sqrt_reference_variance_modulus (d N : ℕ) (hd : 3 ≤ d) (hN : 0 < N)
    (z w : ℂ) (η₀ : ℝ) (hη : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im) :
    |Real.sqrt ((graphKestenMcKayReference d z).im / ((N : ℝ) * z.im)) -
      Real.sqrt ((graphKestenMcKayReference d w).im / ((N : ℝ) * w.im))| ≤
      Real.sqrt ((8 / ((N : ℝ) * η₀ ^ 2)) * dist z w) := by
  have hzp := hη.trans_le hz
  have hwp := hη.trans_le hw
  have himz : 0 ≤ (graphKestenMcKayReference d z).im :=
    (kestenMcKayTransform_im_pos d (semicircleRoot z) z hzp (semicircleRoot_im_pos hzp).le).le
  have himw : 0 ≤ (graphKestenMcKayReference d w).im :=
    (kestenMcKayTransform_im_pos d (semicircleRoot w) w hwp (semicircleRoot_im_pos hwp).le).le
  have ha : 0 ≤ (graphKestenMcKayReference d z).im / ((N : ℝ) * z.im) := by positivity
  have hb : 0 ≤ (graphKestenMcKayReference d w).im / ((N : ℝ) * w.im) := by positivity
  exact (sqrt_holder_bound _ _ ha hb).trans (Real.sqrt_le_sqrt
    (normalized_reference_variance_lipschitz d N hd hN z w η₀ hη hz hw))

/-- The fractional-power contribution has a concrete ordinary Lipschitz
modulus on a positive lower spectral scale. -/
theorem fractional_error_lipschitz (N : ℕ) (hN : 0 < N) (z w : ℂ)
    (η₀ : ℝ) (hη : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im) :
    |(((N : ℝ) * z.im) ^ (2 / 3 : ℝ))⁻¹ - (((N : ℝ) * w.im) ^ (2 / 3 : ℝ))⁻¹| ≤
      ((2 / 3 : ℝ) * ((N : ℝ) * η₀) ^ (- (5 / 3 : ℝ)) * (N : ℝ)) * dist z w := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hzp := hη.trans_le hz
  have hwp := hη.trans_le hw
  rw [← Real.rpow_neg (mul_pos hNp hzp).le, ← Real.rpow_neg (mul_pos hNp hwp).le]
  have h := inverse_two_thirds_lipschitz ((N : ℝ) * η₀) ((N : ℝ) * z.im) ((N : ℝ) * w.im)
    (mul_pos hNp hη) (mul_le_mul_of_nonneg_left hz hNp.le)
    (mul_le_mul_of_nonneg_left hw hNp.le)
  have himdiff : |z.im - w.im| ≤ dist z w := by
    simpa only [dist_eq_norm, Complex.sub_im] using Complex.abs_im_le_norm (z - w)
  have hscale : |(N : ℝ) * z.im - (N : ℝ) * w.im| ≤ (N : ℝ) * dist z w := by
    rw [← mul_sub, abs_mul, abs_of_pos hNp]
    exact mul_le_mul_of_nonneg_left himdiff hNp.le
  exact h.trans (by
    calc
      _ ≤ ((2 / 3 : ℝ) * ((N : ℝ) * η₀) ^ (- (5 / 3 : ℝ))) * ((N : ℝ) * dist z w) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by ring)

/-- The full uninflated error has an explicit half-Hölder plus Lipschitz
modulus. Its localization contribution is constant in the spectral parameter. -/
theorem paperBaseError_modulus (a d N r : ℕ) (hd : 3 ≤ d) (hN : 0 < N)
    (z w : ℂ) (η₀ : ℝ) (hη : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im) :
    |paperBaseError a d N r z.im (graphKestenMcKayReference d z).im -
      paperBaseError a d N r w.im (graphKestenMcKayReference d w).im| ≤
      Real.log (N : ℝ) ^ (8 * a) *
        (Real.sqrt ((8 / ((N : ℝ) * η₀ ^ 2)) * dist z w) +
          ((2 / 3 : ℝ) * ((N : ℝ) * η₀) ^ (- (5 / 3 : ℝ)) * (N : ℝ)) * dist z w) := by
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt hN))
  have hpow : 0 ≤ Real.log (N : ℝ) ^ (8 * a) := pow_nonneg hlog _
  have hroot := sqrt_reference_variance_modulus d N hd hN z w η₀ hη hz hw
  have hfraction := fractional_error_lipschitz N hN z w η₀ hη hz hw
  unfold paperBaseError baseError baseErrorTerms
  rw [← mul_sub, abs_mul, abs_of_nonneg hpow]
  apply mul_le_mul_of_nonneg_left _ hpow
  have hid : ∀ A B C D E : ℝ, (A + B + C) - (A + D + E) = (B - D) + (C - E) := by
    intros
    ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hroot hfraction)


end LocalLaw
