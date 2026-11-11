import SpectralConsequences.SquareRootCDF

/-! # Quantile rigidity from actual finite counts and reference interval mass -/

open Set
noncomputable section
namespace SpectralConsequences
namespace SquareRootCDF

theorem mass_abs_le (P : SquareRootCDF) (x y : ℝ)
    (hx : x ∈ Icc P.lower P.upper) (hy : y ∈ Icc P.lower P.upper) :
    P.mass * |x-y| * Real.sqrt |x-y| ≤ |P.cdf x-P.cdf y| := by
  by_cases hxy : x ≤ y
  · have hm := P.lower_mass x y hx.1 hxy hy.2
    have hF := P.monotone hxy
    simpa only [abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr hF),neg_sub] using hm
  · have hyx := le_of_not_ge hxy
    have hm := P.lower_mass y x hy.1 hyx hx.2
    have hF := P.monotone hyx
    simpa only [abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr hF)] using hm

theorem inverse_modulus (P : SquareRootCDF) (x y δ : ℝ)
    (hx : x ∈ Icc P.lower P.upper) (hy : y ∈ Icc P.lower P.upper)
    (hδ : 0 ≤ δ) (herror : |P.cdf x-P.cdf y| ≤ δ) :
    |x-y| ≤ (δ/P.mass)^(2/3 : ℝ) := by
  have hgap : 0 ≤ |x-y| := abs_nonneg _
  have hm := (P.mass_abs_le x y hx hy).trans herror
  have hm0 : 0 ≤ P.mass * |x-y| * Real.sqrt |x-y| :=
    mul_nonneg (mul_nonneg P.mass_pos.le hgap) (Real.sqrt_nonneg _)
  have hs : (P.mass * |x-y| * Real.sqrt |x-y|)^2 ≤ δ^2 :=
    (sq_le_sq₀ hm0 hδ).mpr hm
  have heq : (P.mass * |x-y| * Real.sqrt |x-y|)^2=P.mass^2*|x-y| ^ 3 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt hgap]
    ring
  rw [heq] at hs
  have hcube : |x-y| ^ 3 ≤ (δ/P.mass)^2 := by
    rw [div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos P.mass_pos)).mpr
    nlinarith only [hs]
  have hr := Real.rpow_le_rpow (pow_nonneg hgap 3) hcube
    (by norm_num : 0 ≤ (3 : ℝ)⁻¹)
  have he3 : (|x-y| ^ 3)^((3 : ℝ)⁻¹)=|x-y| := by
    exact Real.pow_rpow_inv_natCast hgap (by decide : (3 : ℕ)≠0)
  rw [he3] at hr
  rw [←Real.rpow_natCast_mul (div_nonneg hδ P.mass_pos.le)] at hr
  norm_num at hr ⊢
  exact hr

theorem clamped_quantile_error (P : SquareRootCDF) {N : ℕ}
    (values : Fin N → ℝ) (hsort : Antitone values) (δ : ℝ) (hδ : 0 ≤ δ)
    (hcompare : ∀ E, |empiricalCDF values E - P.cdf E| ≤ δ) (i : Fin N) :
    |P.toCompactCDF.clip (values i)-P.toCompactCDF.quantile i| ≤
      (δ/P.mass)^(2/3 : ℝ) := by
  apply P.inverse_modulus _ _ δ (P.toCompactCDF.clip_mem _) (P.toCompactCDF.quantile_mem _) hδ
  rw [P.toCompactCDF.cdf_clip,P.toCompactCDF.cdf_quantile]
  exact referenceCDF_at_ordered_value values hsort P.cdf P.continuous δ hcompare i

/-- Confinement and CDF comparison imply genuine, unclamped quantile positions. -/
theorem rigidity_of_cdf_and_confinement (P : SquareRootCDF) {N : ℕ}
    (values : Fin N → ℝ) (hsort : Antitone values) (δ Δ : ℝ)
    (hδ : 0 ≤ δ) (hΔ : 0 ≤ Δ)
    (hcompare : ∀ E, |empiricalCDF values E - P.cdf E| ≤ δ)
    (i : Fin N) (hlo : P.lower-Δ ≤ values i) (hhi : values i ≤ P.upper+Δ) :
    |values i-P.toCompactCDF.quantile i| ≤ Δ+(δ/P.mass)^(2/3 : ℝ) := by
  have hclip := P.toCompactCDF.sub_clip_abs_le (values i) Δ hΔ hlo hhi
  have hquant := P.clamped_quantile_error values hsort δ hδ hcompare i
  exact (abs_sub_le (values i) (P.toCompactCDF.clip (values i)) (P.toCompactCDF.quantile i)).trans
    (add_le_add hclip hquant)

end SquareRootCDF
end SpectralConsequences
