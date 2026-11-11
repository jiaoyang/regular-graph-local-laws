import SpectralConsequences.KestenMcKayCDF

/-! # The actual reference CDF has the actual bounded-density modulus -/

open Set MeasureTheory
noncomputable section
namespace SpectralConsequences

theorem kestenMcKayClip_abs_sub_le (x y : ℝ) :
    |kestenMcKayClip x-kestenMcKayClip y| ≤ |x-y| := by
  have hmax := abs_max_sub_max_le_max (-2 : ℝ) (min 2 x) (-2) (min 2 y)
  have hmin := abs_min_sub_min_le_max (2 : ℝ) x 2 y
  simp only [sub_self,abs_zero,max_eq_right (abs_nonneg (min 2 x-min 2 y))] at hmax
  simp only [sub_self,abs_zero,max_eq_right (abs_nonneg (x-y))] at hmin
  exact hmax.trans hmin

theorem kestenMcKayCDF_clip (d : ℕ) (hd : 3 ≤ d) (x : ℝ) :
    kestenMcKayCDF d (kestenMcKayClip x)=kestenMcKayCDF d x :=
  (kestenMcKayCompactCDF d hd).cdf_clip x

theorem kestenMcKayCDF_increment_le (d : ℕ) (hd : 3 ≤ d)
    (x y : ℝ) (hxy : x ≤ y) :
    kestenMcKayCDF d y-kestenMcKayCDF d x ≤ kestenMcKayDensityCap d*(y-x) := by
  have hc : kestenMcKayClip x ≤ kestenMcKayClip y :=
    max_le_max le_rfl (min_le_min le_rfl hxy)
  have hcontract := kestenMcKayClip_abs_sub_le x y
  rw [abs_of_nonpos (sub_nonpos.mpr hc),neg_sub,
    abs_of_nonpos (sub_nonpos.mpr hxy),neg_sub] at hcontract
  have hprimitive : kestenMcKayCDF d y-kestenMcKayCDF d x=
      ∫u in kestenMcKayClip x..kestenMcKayClip y,LocalLaw.kestenMcKayDensity d u := by
    have hh := kestenMcKayCDF_sub d hd (kestenMcKayClip_mem x).1 hc (kestenMcKayClip_mem y).2
    simpa only [kestenMcKayCDF_clip d hd] using hh
  have hbound := intervalIntegral.integral_mono_on hc
    (kestenMcKayDensity_between_integrable d hd (kestenMcKayClip_mem x).1 hc (kestenMcKayClip_mem y).2)
    (intervalIntegrable_const (c := kestenMcKayDensityCap d))
    (fun u _ => kestenMcKayDensity_le_cap d hd u)
  rw [intervalIntegral.integral_const,smul_eq_mul] at hbound
  rw [hprimitive]
  exact hbound.trans (by
    have hh := mul_le_mul_of_nonneg_left hcontract (kestenMcKayDensityCap_positive d hd).le
    nlinarith only [hh])

theorem kestenMcKayCDF_abs_sub_le (d : ℕ) (hd : 3 ≤ d) (x y : ℝ) :
    |kestenMcKayCDF d x-kestenMcKayCDF d y| ≤ kestenMcKayDensityCap d*|x-y| := by
  by_cases hxy : x ≤ y
  · rw [abs_of_nonpos (sub_nonpos.mpr (kestenMcKayCDF_monotone d hd hxy)),neg_sub,
      abs_of_nonpos (sub_nonpos.mpr hxy),neg_sub]
    exact kestenMcKayCDF_increment_le d hd x y hxy
  · have hyx := le_of_not_ge hxy
    rw [abs_of_nonneg (sub_nonneg.mpr (kestenMcKayCDF_monotone d hd hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact kestenMcKayCDF_increment_le d hd y x hyx

end SpectralConsequences
