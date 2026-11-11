import LocalLaw.ReferenceBounds
import LocalLaw.VerticalBudgets

/-!
# Vertical monotonicity of the physical regular-tree reference

The proof is algebraic: squared norm parameterizes the physical quadratic
root at fixed real part. No unproved Stieltjes integral representation is used.
-/

namespace LocalLaw

/-- Imaginary part squared as a rational function of the small root's norm
squared, at a fixed real spectral coordinate. -/
noncomputable def semicircleEtaCurve (E t : ℝ) : ℝ :=
  (1 - t) ^ 2 / t - E ^ 2 * (1 - t) ^ 2 / (1 + t) ^ 2

private theorem etaCurve_difference (E t u : ℝ)
    (ht : t ≠ 0) (hu : u ≠ 0) (ht₁ : 1 + t ≠ 0) (hu₁ : 1 + u ≠ 0) :
    semicircleEtaCurve E t - semicircleEtaCurve E u =
      (t - u) * (1 - 1 / (t * u) +
        4 * E ^ 2 * (1 - t * u) / ((1 + t) ^ 2 * (1 + u) ^ 2)) := by
  unfold semicircleEtaCurve
  field_simp
  ring

/-- The two-point strict antitonicity argument uses the admissibility bound
only at the larger norm parameter; no derivative interval is assumed. -/
theorem semicircleEtaCurve_strictAnti (E t u : ℝ)
    (ht : 0 < t) (htu : t < u) (hu : u < 1)
    (admissible : E ^ 2 ≤ (1 + u) ^ 2 / u) :
    semicircleEtaCurve E u < semicircleEtaCurve E t := by
  have hup : 0 < u := ht.trans htu
  have htp : t < 1 := htu.trans hu
  have htuone : t * u < 1 := by
    have h := mul_lt_mul_of_pos_left hu ht
    nlinarith
  have hden : 0 < (1 + t) ^ 2 * (1 + u) ^ 2 := by positivity
  have hmult : 0 ≤ 4 * (1 - t * u) / ((1 + t) ^ 2 * (1 + u) ^ 2) :=
    div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr htuone.le)) hden.le
  have hcomp := mul_le_mul_of_nonneg_left admissible hmult
  have hupper : 1 - 1 / (t * u) +
      4 * E ^ 2 * (1 - t * u) / ((1 + t) ^ 2 * (1 + u) ^ 2) ≤
      -(1 - t * u) * (1 - t) ^ 2 / (t * u * (1 + t) ^ 2) := by
    have halgebra : 1 - 1 / (t * u) +
        (4 * (1 - t * u) / ((1 + t) ^ 2 * (1 + u) ^ 2)) * ((1 + u) ^ 2 / u) =
        -(1 - t * u) * (1 - t) ^ 2 / (t * u * (1 + t) ^ 2) := by
      field_simp
      ring
    rw [← halgebra]
    have heq : 4 * E ^ 2 * (1 - t * u) / ((1 + t) ^ 2 * (1 + u) ^ 2) =
        (4 * (1 - t * u) / ((1 + t) ^ 2 * (1 + u) ^ 2)) * E ^ 2 := by ring
    rw [heq]
    exact add_le_add_left hcomp _
  have hnegative : -(1 - t * u) * (1 - t) ^ 2 / (t * u * (1 + t) ^ 2) < 0 := by
    apply div_neg_of_neg_of_pos
    · have hs : 0 < (1 - t) ^ 2 := sq_pos_of_pos (by linarith)
      nlinarith
    · positivity
  have hbracket : 1 - 1 / (t * u) +
      4 * E ^ 2 * (1 - t * u) / ((1 + t) ^ 2 * (1 + u) ^ 2) < 0 :=
    hupper.trans_lt hnegative
  have hdiff := etaCurve_difference E t u (ne_of_gt ht) (ne_of_gt hup)
    (by positivity) (by positivity)
  have hpositive : 0 < semicircleEtaCurve E t - semicircleEtaCurve E u := by
    rw [hdiff]
    exact mul_pos_of_neg_of_neg (sub_neg.mpr htu) hbracket
  linarith

/-- The real part of the physical-root polynomial after multiplication by
its complex conjugate. -/
theorem cavity_root_real_identity {m z : ℂ} (hm : m ^ 2 + z * m + 1 = 0) :
    m.re * (1 + ‖m‖ ^ 2) = -z.re * ‖m‖ ^ 2 := by
  have hnorm : m * star m = (‖m‖ ^ 2 : ℝ) := by
    simpa only [Complex.normSq_eq_norm_sq] using Complex.mul_conj m
  have hmult : (m + z) * (‖m‖ ^ 2 : ℝ) + star m = 0 := by
    calc
      (m + z) * (‖m‖ ^ 2 : ℝ) + star m =
          (m ^ 2 + z * m + 1) * star m := by rw [← hnorm]; ring
      _ = 0 := by rw [hm]; simp
  have hre := congrArg Complex.re hmult
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_im,
    Complex.ofReal_re, mul_zero, sub_zero, Complex.star_def, Complex.conj_re,
    Complex.zero_re] at hre
  nlinarith

/-- Admissibility of the real spectral coordinate as a function of norm
squared; the bound is proved from the actual root equation. -/
theorem cavity_root_real_admissible {m z : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) :
    z.re ^ 2 ≤ (1 + ‖m‖ ^ 2) ^ 2 / (‖m‖ ^ 2) := by
  have hpos : 0 < ‖m‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (cavity_root_ne_zero hm))
  have hre := cavity_root_real_identity hm
  have hsq := congrArg (fun x : ℝ => x ^ 2) hre
  dsimp only at hsq
  have hn : ‖m‖ ^ 2 = m.re ^ 2 + m.im ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.sq_norm m
  have hcomp : m.re ^ 2 ≤ ‖m‖ ^ 2 := by nlinarith [sq_nonneg m.im]
  have hmul := mul_le_mul_of_nonneg_right hcomp (sq_nonneg (1 + ‖m‖ ^ 2))
  have hscaled : z.re ^ 2 * ‖m‖ ^ 2 ≤ (1 + ‖m‖ ^ 2) ^ 2 := by
    apply (mul_le_mul_right hpos).mp
    nlinarith [hsq]
  exact (le_div_iff₀ hpos).2 hscaled

/-- The physical quadratic root satisfies the rational norm parameterization. -/
theorem cavity_root_etaCurve {m z : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hnorm : ‖m‖ ≤ 1) :
    z.im ^ 2 = semicircleEtaCurve z.re (‖m‖ ^ 2) := by
  have hpos : 0 < ‖m‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (cavity_root_ne_zero hm))
  have hlt : ‖m‖ ^ 2 < 1 := by
    have h := (physical_cavity_root hm hz hnorm).1
    nlinarith [norm_nonneg m]
  have hp : 1 + ‖m‖ ^ 2 ≠ 0 := by positivity
  have hm₁ : 1 - ‖m‖ ^ 2 ≠ 0 := by linarith
  have ha : m.re = -z.re * ‖m‖ ^ 2 / (1 + ‖m‖ ^ 2) :=
    (eq_div_iff hp).2 (cavity_root_real_identity hm)
  have hb : m.im = z.im * ‖m‖ ^ 2 / (1 - ‖m‖ ^ 2) := by
    apply (eq_div_iff hm₁).2
    exact (cavity_root_imaginary_identity hm).symm
  have hn : ‖m‖ ^ 2 = m.re ^ 2 + m.im ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.sq_norm m
  rw [ha, hb] at hn
  unfold semicircleEtaCurve
  field_simp at hn ⊢
  nlinarith [hn]

/-- For fixed real coordinate, the physical root's squared norm decreases
as the positive imaginary spectral coordinate increases. -/
theorem physical_cavity_normSq_antitone_im {a b z w : ℂ}
    (ha : a ^ 2 + z * a + 1 = 0) (hb : b ^ 2 + w * b + 1 = 0)
    (hz : 0 < z.im) (hw : 0 < w.im) (hreal : z.re = w.re) (him : z.im ≤ w.im)
    (hanorm : ‖a‖ ≤ 1) (hbnorm : ‖b‖ ≤ 1) : ‖b‖ ^ 2 ≤ ‖a‖ ^ 2 := by
  have hap : 0 < ‖a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (cavity_root_ne_zero ha))
  have hbp : 0 < ‖b‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (cavity_root_ne_zero hb))
  have hblt : ‖b‖ ^ 2 < 1 := by
    have h := (physical_cavity_root hb hw hbnorm).1
    nlinarith [norm_nonneg b]
  by_contra h
  have hlt : ‖a‖ ^ 2 < ‖b‖ ^ 2 := lt_of_not_ge h
  have hadmissible := cavity_root_real_admissible hb
  rw [← hreal] at hadmissible
  have hcurve := semicircleEtaCurve_strictAnti z.re (‖a‖ ^ 2) (‖b‖ ^ 2)
    hap hlt hblt hadmissible
  rw [← cavity_root_etaCurve ha hz hanorm, hreal,
    ← cavity_root_etaCurve hb hw hbnorm] at hcurve
  nlinarith



noncomputable def treeVarianceCoordinate (k t : ℝ) : ℝ := t / ((1 + t) * (k + t))
noncomputable def treeVarianceBase (k t : ℝ) : ℝ := k * t / ((1 - t) * (k + t))
noncomputable def treeVarianceCorrection (k E t : ℝ) : ℝ :=
  4 * k * E ^ 2 * treeVarianceCoordinate k t ^ 2
noncomputable def treeVarianceCurve (k E t : ℝ) : ℝ :=
  treeVarianceBase k t / (1 - treeVarianceCorrection k E t)

theorem treeVarianceCoordinate_mono (k t u : ℝ) (hk : 2 ≤ k)
    (ht : 0 < t) (htu : t ≤ u) (hu : u < 1) :
    treeVarianceCoordinate k t ≤ treeVarianceCoordinate k u := by
  have hup : 0 < u := ht.trans_le htu
  have htl : t < 1 := htu.trans_lt hu
  have htuone : t * u < 1 := by
    have h := mul_lt_mul_of_pos_left hu ht
    nlinarith
  unfold treeVarianceCoordinate
  apply (div_le_div_iff₀ (by positivity : 0 < (1 + t) * (k + t))
    (by positivity : 0 < (1 + u) * (k + u))).2
  have h : 0 ≤ (u - t) * (k - t * u) :=
    mul_nonneg (sub_nonneg.mpr htu) (by linarith)
  nlinarith

theorem treeVarianceBase_mono (k t u : ℝ) (hk : 2 ≤ k)
    (ht : 0 < t) (htu : t ≤ u) (hu : u < 1) :
    treeVarianceBase k t ≤ treeVarianceBase k u := by
  have hup : 0 < u := ht.trans_le htu
  have htl : t < 1 := htu.trans_lt hu
  have h1t : 0 < 1 - t := by linarith
  have h1u : 0 < 1 - u := by linarith
  have hkp : 0 < k := by linarith
  have hdiff : 0 ≤ u - t := sub_nonneg.mpr htu
  unfold treeVarianceBase
  apply (div_le_div_iff₀ (by positivity : 0 < (1 - t) * (k + t))
    (by positivity : 0 < (1 - u) * (k + u))).2
  have h : 0 ≤ k * (u - t) * (k + t * u) := by positivity
  nlinarith

theorem treeVarianceCorrection_mono (k E t u : ℝ) (hk : 2 ≤ k)
    (ht : 0 < t) (htu : t ≤ u) (hu : u < 1) :
    treeVarianceCorrection k E t ≤ treeVarianceCorrection k E u := by
  have hcoord := treeVarianceCoordinate_mono k t u hk ht htu hu
  have hnonneg : 0 ≤ treeVarianceCoordinate k t := by
    unfold treeVarianceCoordinate
    positivity
  have hsq : treeVarianceCoordinate k t ^ 2 ≤ treeVarianceCoordinate k u ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 4 * k * E ^ 2)

/-- Admissibility keeps the rational variance denominator positive. -/
theorem treeVariance_denominator_pos (k E t : ℝ) (hk : 2 ≤ k)
    (ht : 0 < t) (htl : t < 1) (admissible : E ^ 2 ≤ (1 + t) ^ 2 / t) :
    0 < 1 - treeVarianceCorrection k E t := by
  have hkpos : 0 < k := by linarith
  have hkt : 0 < k + t := by positivity
  have hkt0 : k + t ≠ 0 := ne_of_gt hkt
  have htp0 : 1 + t ≠ 0 := by positivity
  have hcoef : 0 ≤ 4 * k * treeVarianceCoordinate k t ^ 2 := by positivity
  have hbound := mul_le_mul_of_nonneg_left admissible hcoef
  have hA : treeVarianceCorrection k E t ≤ 4 * k * t / (k + t) ^ 2 := by
    have h₁ : treeVarianceCorrection k E t = (4 * k * treeVarianceCoordinate k t ^ 2) * E ^ 2 := by
      unfold treeVarianceCorrection
      ring
    have h₂ : (4 * k * treeVarianceCoordinate k t ^ 2) * ((1 + t) ^ 2 / t) =
        4 * k * t / (k + t) ^ 2 := by
      unfold treeVarianceCoordinate
      field_simp
      ring
    rw [h₁, ← h₂]
    exact hbound
  have hratio : 4 * k * t / (k + t) ^ 2 < 1 := by
    apply (div_lt_one (sq_pos_of_pos hkt)).2
    have hsq : 0 < (k - t) ^ 2 := sq_pos_of_pos (by linarith)
    nlinarith
  linarith

/-- The regular-tree variance curve is increasing in norm squared. -/
theorem treeVarianceCurve_mono (k E t u : ℝ) (hk : 2 ≤ k)
    (ht : 0 < t) (htu : t ≤ u) (hu : u < 1)
    (admissible : E ^ 2 ≤ (1 + u) ^ 2 / u) :
    treeVarianceCurve k E t ≤ treeVarianceCurve k E u := by
  have hup : 0 < u := ht.trans_le htu
  have hbase := treeVarianceBase_mono k t u hk ht htu hu
  have hA := treeVarianceCorrection_mono k E t u hk ht htu hu
  have hden := treeVariance_denominator_pos k E u hk hup hu admissible
  have hnonneg : 0 ≤ treeVarianceBase k u := by
    unfold treeVarianceBase
    exact div_nonneg (mul_nonneg (by linarith) hup.le)
      (mul_nonneg (by linarith) (by linarith))
  exact div_le_div₀ hnonneg hbase hden (by linarith)

private theorem rationalTreeReference_im_formula (k : ℕ) (hk : 0 < k) (m : ℂ) :
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

private theorem rationalTreeReference_denominator_normSq (k : ℕ) (hk : 0 < k) (m : ℂ) :
    Complex.normSq (1 - m ^ 2 / (k : ℂ)) =
      (((k : ℝ) + ‖m‖ ^ 2) ^ 2 - 4 * (k : ℝ) * m.re ^ 2) / (k : ℝ) ^ 2 := by
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hk)
  have hn : ‖m‖ ^ 2 = m.re ^ 2 + m.im ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.sq_norm m
  rw [hn]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.div_re,
    Complex.sub_im, Complex.one_im, Complex.div_im, Complex.natCast_re, Complex.natCast_im,
    mul_zero, zero_mul, add_zero, sub_zero, pow_two, Complex.mul_re, Complex.mul_im]
  field_simp
  ring



/-- The actual normalized imaginary part is the positive rational variance
curve in the squared norm of the physical semicircle root. -/
theorem rationalTreeReference_variance_curve (k : ℕ) (hk : 2 ≤ k) {m z : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hnorm : ‖m‖ ≤ 1) :
    (rationalTreeReference k m).im / z.im = treeVarianceCurve (k : ℝ) z.re (‖m‖ ^ 2) := by
  have hkp : 0 < k := by omega
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hkp
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have ht : 0 < ‖m‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (cavity_root_ne_zero hm))
  have htl : ‖m‖ ^ 2 < 1 := by
    have h := (physical_cavity_root hm hz hnorm).1
    nlinarith [norm_nonneg m]
  have htp : 1 + ‖m‖ ^ 2 ≠ 0 := by positivity
  have htm : 1 - ‖m‖ ^ 2 ≠ 0 := by linarith
  have hkt : (k : ℝ) + ‖m‖ ^ 2 ≠ 0 := by positivity
  have ha : m.re = -z.re * ‖m‖ ^ 2 / (1 + ‖m‖ ^ 2) :=
    (eq_div_iff htp).2 (cavity_root_real_identity hm)
  have hb : m.im / z.im = ‖m‖ ^ 2 / (1 - ‖m‖ ^ 2) := by
    apply (div_eq_div_iff (ne_of_gt hz) htm).2
    simpa only [mul_comm] using (cavity_root_imaginary_identity hm).symm
  have hden := treeVariance_denominator_pos (k : ℝ) z.re (‖m‖ ^ 2) hkr ht htl
    (cavity_root_real_admissible hm)
  have hfactor : Complex.normSq (1 - m ^ 2 / (k : ℂ)) =
      (((k : ℝ) + ‖m‖ ^ 2) ^ 2 / (k : ℝ) ^ 2) *
        (1 - treeVarianceCorrection (k : ℝ) z.re (‖m‖ ^ 2)) := by
    rw [rationalTreeReference_denominator_normSq k hkp m, ha]
    unfold treeVarianceCorrection treeVarianceCoordinate
    field_simp
    ring
  calc
    (rationalTreeReference k m).im / z.im =
        (m.im / z.im) * (1 + ‖m‖ ^ 2 / (k : ℝ)) /
          Complex.normSq (1 - m ^ 2 / (k : ℂ)) := by
      rw [rationalTreeReference_im_formula k hkp m]
      ring
    _ = (‖m‖ ^ 2 / (1 - ‖m‖ ^ 2)) * (1 + ‖m‖ ^ 2 / (k : ℝ)) /
        ((((k : ℝ) + ‖m‖ ^ 2) ^ 2 / (k : ℝ) ^ 2) *
          (1 - treeVarianceCorrection (k : ℝ) z.re (‖m‖ ^ 2))) := by rw [hb, hfactor]
    _ = treeVarianceCurve (k : ℝ) z.re (‖m‖ ^ 2) := by
      unfold treeVarianceCurve treeVarianceBase
      field_simp
      ring

/-- Actual regular-tree reference variance decreases under vertical motion
in the upper half-plane. Both the physical branch and monotonicity are proved. -/
theorem rationalTreeReference_variance_antitone_im (k : ℕ) (hk : 2 ≤ k)
    {a b z w : ℂ}
    (ha : a ^ 2 + z * a + 1 = 0) (hb : b ^ 2 + w * b + 1 = 0)
    (hz : 0 < z.im) (hw : 0 < w.im) (hreal : z.re = w.re) (him : z.im ≤ w.im)
    (hanorm : ‖a‖ ≤ 1) (hbnorm : ‖b‖ ≤ 1) :
    (rationalTreeReference k b).im / w.im ≤ (rationalTreeReference k a).im / z.im := by
  rw [rationalTreeReference_variance_curve k hk hb hw hbnorm,
    rationalTreeReference_variance_curve k hk ha hz hanorm, ← hreal]
  have hbpos : 0 < ‖b‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (cavity_root_ne_zero hb))
  have halt : ‖a‖ ^ 2 < 1 := by
    have h := (physical_cavity_root ha hz hanorm).1
    nlinarith [norm_nonneg a]
  exact treeVarianceCurve_mono (k : ℝ) z.re (‖b‖ ^ 2) (‖a‖ ^ 2)
    (by exact_mod_cast hk) hbpos
    (physical_cavity_normSq_antitone_im ha hb hz hw hreal him hanorm hbnorm)
    halt (cavity_root_real_admissible ha)

/-- The Kesten--McKay reference used by the graph local law satisfies the
vertical variance monotonicity required by the error-budget argument. -/
theorem kestenMcKayTransform_variance_antitone_im (d : ℕ) (hd : 3 ≤ d) (z w : ℂ)
    (hz : 0 < z.im) (hw : 0 < w.im) (hreal : z.re = w.re) (him : z.im ≤ w.im) :
    (kestenMcKayTransform d (semicircleRoot w) w).im / w.im ≤
      (kestenMcKayTransform d (semicircleRoot z) z).im / z.im := by
  rw [kestenMcKayTransform_eq d hd _ w (semicircleRoot_equation w) hw
    (semicircleRoot_im_pos hw).le,
    kestenMcKayTransform_eq d hd _ z (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le]
  exact rationalTreeReference_variance_antitone_im (d - 1) (by omega)
    (semicircleRoot_equation z) (semicircleRoot_equation w) hz hw hreal him
    (semicircleRoot_norm_le_one z) (semicircleRoot_norm_le_one w)



/-- Equation (4.2) increases along a downward vertical spectral step. This
uses the actual reference variance monotonicity, not an assumed base-error
ordering. -/
theorem paperBaseError_antitone_im (a d N r : ℕ) (hd : 3 ≤ d) (hN : 0 < N)
    (z w : ℂ) (hz : 0 < z.im) (hw : 0 < w.im)
    (hreal : z.re = w.re) (him : z.im ≤ w.im) :
    paperBaseError a d N r w.im (kestenMcKayTransform d (semicircleRoot w) w).im ≤
      paperBaseError a d N r z.im (kestenMcKayTransform d (semicircleRoot z) z).im := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hvariance := kestenMcKayTransform_variance_antitone_im d hd z w hz hw hreal him
  have hnormalized : (kestenMcKayTransform d (semicircleRoot w) w).im / ((N : ℝ) * w.im) ≤
      (kestenMcKayTransform d (semicircleRoot z) z).im / ((N : ℝ) * z.im) := by
    calc
      _ = ((kestenMcKayTransform d (semicircleRoot w) w).im / w.im) / (N : ℝ) := by
        rw [mul_comm (N : ℝ) w.im, div_mul_eq_div_div]
      _ ≤ ((kestenMcKayTransform d (semicircleRoot z) z).im / z.im) / (N : ℝ) :=
        div_le_div_of_nonneg_right hvariance hNpos.le
      _ = _ := by rw [mul_comm (N : ℝ) z.im, div_mul_eq_div_div]
  have hpow : ((N : ℝ) * z.im) ^ (2 / 3 : ℝ) ≤ ((N : ℝ) * w.im) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow (mul_pos hNpos hz).le
      (mul_le_mul_of_nonneg_left him hNpos.le) (by norm_num)
  have hsample := one_div_le_one_div_of_le
    (Real.rpow_pos_of_pos (mul_pos hNpos hz) (2 / 3 : ℝ)) hpow
  have hinv : (((N : ℝ) * w.im) ^ (2 / 3 : ℝ))⁻¹ ≤
      (((N : ℝ) * z.im) ^ (2 / 3 : ℝ))⁻¹ := by simpa only [one_div] using hsample
  have hsqrt := Real.sqrt_le_sqrt hnormalized
  unfold paperBaseError baseError baseErrorTerms
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hlog _)
  linarith

/-- The actual discontinuous error and its scalar stability budget increase
along downward vertical motion, including threshold-branch changes. -/
theorem paperError_vertical_budgets (a d N r : ℕ) (hd : 3 ≤ d) (hN : 0 < N)
    (z w : ℂ) (hz : 0 < z.im) (hw : 0 < w.im)
    (hreal : z.re = w.re) (him : z.im ≤ w.im) (hlog : 1 ≤ Real.log (N : ℝ)) :
    paperError a d N r w (kestenMcKayTransform d (semicircleRoot w) w).im ≤
      paperError a d N r z (kestenMcKayTransform d (semicircleRoot z) z).im ∧
    scalarScale (spectralScale w)
        (paperError a d N r w (kestenMcKayTransform d (semicircleRoot w) w).im) ≤
      scalarScale (spectralScale z)
        (paperError a d N r z (kestenMcKayTransform d (semicircleRoot z) z).im) := by
  have hbase := paperBaseError_antitone_im a d N r hd hN z w hz hw hreal him
  have hbase0 : 0 ≤ paperBaseError a d N r w.im
      (kestenMcKayTransform d (semicircleRoot w) w).im :=
    baseError_nonnegative _ _ _ _ _ _ _ (by linarith) hw.le
  have hscale : spectralScale z ≤ spectralScale w := by
    unfold spectralScale edgeDistance
    rw [hreal]
    linarith
  exact vertical_error_budgets (Real.log (N : ℝ)) _ _ (spectralScale w) (spectralScale z)
    hlog hbase0 hbase (spectralScale_pos hz) hscale

end LocalLaw
