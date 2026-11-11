import LocalLaw.KestenMcKayStieltjes

/-! # Positivity, integrability and exact mass of the Kesten--McKay density -/

open Set Complex MeasureTheory
open scoped BigOperators Interval
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem kestenMcKay_denominator_pos (d : ℕ) (hd : 3 ≤ d) {x : ℝ}
    (hx : x ∈ Icc (-2 : ℝ) 2) : 0 < (kestenMcKayExterior d)^2 - x^2 := by
  have ha := (kestenMcKay_real_parameters d hd).1
  have hx2 : x^2 ≤ 4 := by
    have hh := mul_nonneg (show 0 ≤ x + 2 by linarith [hx.1])
      (show 0 ≤ 2 - x by linarith [hx.2])
    nlinarith
  nlinarith

theorem kestenMcKayDensity_continuousOn (d : ℕ) (hd : 3 ≤ d) :
    ContinuousOn (kestenMcKayDensity d) (Icc (-2 : ℝ) 2) := by
  have hc : ContinuousOn (fun x => (d : ℝ) * semicircleDensity x /
      ((kestenMcKayExterior d)^2 - x^2)) (Icc (-2 : ℝ) 2) :=
    (continuous_const.mul semicircleDensity_continuous).continuousOn.div
      (by fun_prop : Continuous (fun x : ℝ => (kestenMcKayExterior d)^2 - x^2)).continuousOn
      (fun x hx => (kestenMcKay_denominator_pos d hd hx).ne')
  exact hc.congr (fun x _ => kestenMcKayDensity_eq_rational d hd x)

theorem kestenMcKayDensity_intervalIntegrable (d : ℕ) (hd : 3 ≤ d) :
    IntervalIntegrable (kestenMcKayDensity d) volume (-2 : ℝ) 2 :=
  (kestenMcKayDensity_continuousOn d hd).intervalIntegrable_of_Icc (by norm_num)

theorem kestenMcKayDensity_nonnegative (d : ℕ) (hd : 3 ≤ d) (x : ℝ) :
    0 ≤ kestenMcKayDensity d x := by
  by_cases hx : x ∈ Icc (-2 : ℝ) 2
  · rw [kestenMcKayDensity_eq_rational d hd]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (semicircleDensity_nonneg x))
      (kestenMcKay_denominator_pos d hd hx).le
  · rw [kestenMcKayDensity_eq_zero_of_not_mem d x hx]

/-- A uniform comparison with the semicircle density on the full real line. -/
theorem kestenMcKayDensity_ge_semicircle (d : ℕ) (hd : 3 ≤ d) (x : ℝ) :
    (2 / 3 : ℝ) * semicircleDensity x ≤ kestenMcKayDensity d x := by
  by_cases hx : x ∈ Icc (-2 : ℝ) 2
  · have hD : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
    have hk : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hrel : (((d - 1 : ℕ) : ℝ)) = (d : ℝ) - 1 := by
      have hh : (((d - 1 : ℕ) : ℝ)) + 1 = (d : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ d)
      linarith
    have hratio : (d : ℝ) / ((d - 1 : ℕ) : ℝ) ≤ 3 / 2 := by
      apply (div_le_iff₀ hk).mpr
      rw [hrel]
      linarith
    have ha := (kestenMcKay_real_parameters d hd).2.2.2.2.2
    have hden : (2 / 3 : ℝ) * ((kestenMcKayExterior d)^2 - x^2) ≤ d := by
      have hh := mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg (α := ℝ) d)
      rw [ha]
      have he : (d : ℝ)^2 / ((d - 1 : ℕ) : ℝ) =
          ((d : ℝ) / ((d - 1 : ℕ) : ℝ)) * d := by ring
      rw [he]
      nlinarith [sq_nonneg x]
    rw [kestenMcKayDensity_eq_rational d hd]
    apply (le_div_iff₀ (kestenMcKay_denominator_pos d hd hx)).mpr
    have hh := mul_le_mul_of_nonneg_right hden (semicircleDensity_nonneg x)
    nlinarith
  · rw [kestenMcKayDensity_eq_zero_of_not_mem d x hx,
      semicircleDensity_eq_zero_of_not_mem x hx, mul_zero]

def kestenMcKayDensityCap (d : ℕ) : ℝ :=
  (d : ℝ) / (Real.pi * ((kestenMcKayExterior d)^2 - 4))

theorem kestenMcKayDensityCap_positive (d : ℕ) (hd : 3 ≤ d) :
    0 < kestenMcKayDensityCap d := by
  have ha := (kestenMcKay_real_parameters d hd).1
  have hh : 0 < (kestenMcKayExterior d)^2 - 4 := by nlinarith
  unfold kestenMcKayDensityCap
  exact div_pos (Nat.cast_pos.mpr (by omega)) (mul_pos Real.pi_pos hh)

theorem kestenMcKayDensity_le_cap (d : ℕ) (hd : 3 ≤ d) (x : ℝ) :
    kestenMcKayDensity d x ≤ kestenMcKayDensityCap d := by
  by_cases hx : x ∈ Icc (-2 : ℝ) 2
  · have ha := (kestenMcKay_real_parameters d hd).1
    have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
    have hbase : 0 < (kestenMcKayExterior d)^2 - 4 := by nlinarith
    have hx2 : x^2 ≤ 4 := by
      have hh := mul_nonneg (show 0 ≤ x + 2 by linarith [hx.1])
        (show 0 ≤ 2 - x by linarith [hx.2])
      nlinarith
    have hs : Real.sqrt (4 - x^2) ≤ 2 := by
      exact Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [sq_nonneg x]⟩
    have hsemi : semicircleDensity x ≤ 1 / Real.pi := by
      unfold semicircleDensity
      apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
      field_simp
      linarith
    rw [kestenMcKayDensity_eq_rational d hd]
    calc
      _ ≤ (d : ℝ) * (1 / Real.pi) / ((kestenMcKayExterior d)^2 - x^2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsemi hd0)
          (kestenMcKay_denominator_pos d hd hx).le
      _ ≤ (d : ℝ) * (1 / Real.pi) / ((kestenMcKayExterior d)^2 - 4) :=
        div_le_div_of_nonneg_left (by positivity) hbase (by linarith)
      _ = kestenMcKayDensityCap d := by
        unfold kestenMcKayDensityCap
        field_simp
  · rw [kestenMcKayDensity_eq_zero_of_not_mem d x hx]
    exact (kestenMcKayDensityCap_positive d hd).le

/-- Exact normalization, evaluated by real exterior semicircle integrals. -/
theorem kestenMcKayDensity_integral (d : ℕ) (hd : 3 ≤ d) :
    (∫ x in (-2 : ℝ)..2, kestenMcKayDensity d x) = 1 := by
  let a := kestenMcKayExterior d
  let w := kestenMcKayExteriorRoot d
  obtain ⟨ha, hw, hw1, hquad, hwa, _⟩ := kestenMcKay_real_parameters d hd
  have hden := exterior_semicircle_denominator a ha
  have hw' : 0 < w := hw
  have hnorm : ‖(w : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw'] using hw1
  have heq : (w : ℂ)^2 - (a : ℂ) * w + 1 = 0 := by exact_mod_cast hquad
  have hp := physical_root_density_interval_integral (-w : ℂ) (a : ℂ)
    (by linear_combination heq) (by simpa only [norm_neg] using hnorm) hden.1
  have hn := physical_root_density_interval_integral (w : ℂ) (-a : ℂ)
    (by linear_combination heq) hnorm hden.2
  have hplus : ContinuousOn (fun x : ℝ => (semicircleDensity x : ℂ) / ((x : ℂ) - (a : ℂ)))
      (Icc (-2 : ℝ) 2) :=
    (Complex.continuous_ofReal.comp semicircleDensity_continuous).continuousOn.div
      (by fun_prop : Continuous (fun x : ℝ => (x : ℂ) - (a : ℂ))).continuousOn hden.1
  have hminus : ContinuousOn (fun x : ℝ => (semicircleDensity x : ℂ) / ((x : ℂ) - (-a : ℂ)))
      (Icc (-2 : ℝ) 2) :=
    (Complex.continuous_ofReal.comp semicircleDensity_continuous).continuousOn.div
      (by fun_prop : Continuous (fun x : ℝ => (x : ℂ) - (-a : ℂ))).continuousOn hden.2
  have hpoint : EqOn (fun x : ℝ => (kestenMcKayDensity d x : ℂ))
      (fun x => ((d : ℂ) / (2 * (a : ℂ))) *
        ((semicircleDensity x : ℂ) / ((x : ℂ) - (-a : ℂ)) -
         (semicircleDensity x : ℂ) / ((x : ℂ) - (a : ℂ)))) (uIcc (-2 : ℝ) 2) := by
    intro x hx
    have hx' : x ∈ Icc (-2 : ℝ) 2 := by simpa only [uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 2)] using hx
    have hxp := hden.1 x hx'
    have hxn := hden.2 x hx'
    have hxa : (x : ℂ) + (a : ℂ) ≠ 0 := by simpa only [sub_neg_eq_add] using hxn
    have hax : (a : ℂ) + (x : ℂ) ≠ 0 := by simpa only [add_comm] using hxa
    have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hr : ((a : ℂ)^2 - (x : ℂ)^2) ≠ 0 := by
      simpa only [a, Complex.ofReal_sub, Complex.ofReal_pow] using
        Complex.ofReal_ne_zero.mpr (kestenMcKay_denominator_pos d hd hx').ne'
    dsimp only
    rw [kestenMcKayDensity_eq_rational d hd]
    change (((d : ℝ) * semicircleDensity x / (a^2 - x^2) : ℝ) : ℂ) = _
    push_cast
    field_simp [hxp, hxn, hxa, hax, ha0, hr]
    ring
  have hcomplex : (∫ x in (-2 : ℝ)..2, (kestenMcKayDensity d x : ℂ)) = 1 := by
    rw [intervalIntegral.integral_congr hpoint, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub
        (hminus.intervalIntegrable_of_Icc (by norm_num))
        (hplus.intervalIntegrable_of_Icc (by norm_num)), hn, hp]
    have he : (d : ℂ) * (w : ℂ) / (a : ℂ) = 1 := by
      have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hr : (d : ℝ) * w / a = 1 := by rw [mul_div_assoc, hwa]; field_simp
      exact_mod_cast hr
    convert he using 1
    ring
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  exact hcomplex

end SpectralConsequences
