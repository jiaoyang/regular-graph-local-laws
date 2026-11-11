import LocalLaw.ReferenceBounds
import LocalLaw.ErrorParameters
import LocalLaw.ParameterGrowth

/-!
# Actual finite error smallness from the paper's scale separation

The variance and fractional-power terms are estimated from md<=2 and
N*eta >= (log N)^b. Localization is kept as its own numerical radius budget;
its large-N realization is proved separately from logarithmic radius growth.
-/

open Filter

namespace LocalLaw

private theorem variance_component_small (I X P : ℝ) (hI : I ≤ 2)
    (hP : 0 < P) (hX : 18 * P ^ 2 ≤ X) :
    Real.sqrt (I / X) ≤ 1 / (3 * P) := by
  have hXp : 0 < X := lt_of_lt_of_le (by positivity) hX
  have hright : 0 ≤ 1 / (3 * P) := by positivity
  apply Real.sqrt_le_iff.mpr
  refine ⟨hright, ?_⟩
  calc
    I / X ≤ 2 / X := div_le_div_of_nonneg_right hI hXp.le
    _ ≤ 2 / (18 * P ^ 2) := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (by positivity) hX
    _ = (1 / (3 * P)) ^ 2 := by field_simp; ring

private theorem fractional_component_small (X P : ℝ) (hP : 1 ≤ P)
    (hX : 18 * P ^ 2 ≤ X) :
    (X ^ (2 / 3 : ℝ))⁻¹ ≤ 1 / (3 * P) := by
  have hPp : 0 < P := by linarith
  have hXone : 1 ≤ X := by nlinarith
  have hsqrt : 3 * P ≤ Real.sqrt X := by
    have hsq : (3 * P) ^ 2 ≤ X := by nlinarith
    have hs := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < 3 * P)] at hs
    exact hs
  have hp := Real.rpow_le_rpow_of_exponent_le hXone
    (by norm_num : (1 / 2 : ℝ) ≤ 2 / 3)
  have hden : 3 * P ≤ X ^ (2 / 3 : ℝ) :=
    hsqrt.trans (by simpa only [Real.sqrt_eq_rpow] using hp)
  simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < 3 * P) hden

/-- The source exponent gap b>=25a,a>=12 yields the quantitative
variance scale needed for both random terms. -/
theorem sample_scale_large (L X : ℝ) (a b : ℕ) (hL : 3 ≤ L)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hX : L ^ b ≤ X) :
    18 * (L ^ (12 * a + 4)) ^ 2 ≤ X := by
  have hLone : 1 ≤ L := by linarith
  have hexp : 2 * (12 * a + 4) + 4 ≤ b := by omega
  have hpow : L ^ (2 * (12 * a + 4) + 4) ≤ L ^ b := pow_le_pow_right₀ hLone hexp
  have hfour : (81 : ℝ) ≤ L ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 4
    norm_num at h
    exact h
  calc
    18 * (L ^ (12 * a + 4)) ^ 2 ≤ L ^ (2 * (12 * a + 4)) * L ^ 4 := by
      rw [show 2 * (12 * a + 4) = (12 * a + 4) * 2 by omega, pow_mul]
      nlinarith [sq_nonneg (L ^ (12 * a + 4))]
    _ = L ^ (2 * (12 * a + 4) + 4) := (pow_add ..).symm
    _ ≤ X := hpow.trans hX

/-- The first smallness statement (4.5), with its localization budget explicit. -/
theorem paperError_small_of_radius_budget (a b d N r : ℕ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hN : 0 < N)
    (z : ℂ) (hz : 0 < z.im) (hL : 3 ≤ Real.log (N : ℝ))
    (hscale : Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im)
    (hlocal : (((d - 1 : ℕ) : ℝ) ^ r)⁻¹ ≤
      1 / (3 * Real.log (N : ℝ) ^ (12 * a + 4))) :
    paperError a d N r z (kestenMcKayTransform d (semicircleRoot z) z).im ≤
      (Real.log (N : ℝ) ^ (4 * a))⁻¹ := by
  let L := Real.log (N : ℝ)
  let P := L ^ (12 * a + 4)
  let X := (N : ℝ) * z.im
  have hLp : 0 < L := by dsimp [L]; linarith
  have hPone : 1 ≤ P := one_le_pow₀ (by dsimp [L]; linarith)
  have hPp : 0 < P := by linarith
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hXraw : L ^ b ≤ X := by
    have h := (div_le_iff₀ hNp).mp hscale
    simpa only [L, X, mul_comm] using h
  have hlarge : 18 * P ^ 2 ≤ X := sample_scale_large L X a b hL ha hb hXraw
  have hIm : (kestenMcKayTransform d (semicircleRoot z) z).im ≤ 2 :=
    ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans
      (kestenMcKayTransform_norm_le_two d hd z hz)
  have hvariance := variance_component_small _ X P hIm hPp hlarge
  have hfraction := fractional_component_small X P hPone hlarge
  apply inflatedBaseError_small L a d N r z.im _ (spectralScale z) (by dsimp [L]; linarith) hz.le
  change (((d - 1 : ℕ) : ℝ) ^ r)⁻¹ +
      Real.sqrt ((kestenMcKayTransform d (semicircleRoot z) z).im / X) +
      (X ^ (2 / 3 : ℝ))⁻¹ ≤ P⁻¹
  have hloc : (((d - 1 : ℕ) : ℝ) ^ r)⁻¹ ≤ 1 / (3 * P) := hlocal
  calc
    _ ≤ 1 / (3 * P) + 1 / (3 * P) + 1 / (3 * P) :=
      add_le_add (add_le_add hloc hvariance) hfraction
    _ = P⁻¹ := by
      field_simp [ne_of_gt hPp]
      norm_num

/-- The source error smallness is realized uniformly in the spectral
parameter for all sufficiently large natural N, with the actual logarithmic
integer radius. No localization budget remains as an assumption. -/
theorem eventually_paperError_small (a b d : ℕ) (β : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ, 0 < z.im →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      paperError a d N (logarithmicRadius β d N) z
        (kestenMcKayTransform d (semicircleRoot z) z).im ≤
        (Real.log (N : ℝ) ^ (4 * a))⁻¹ := by
  filter_upwards [eventually_localization_log_budget β d (12 * a + 4) hβ hd,
    eventually_log_ge_nat 3, Filter.eventually_ge_atTop 1] with N hlocal hlog hN
  intro z hz hscale
  exact paperError_small_of_radius_budget a b d N _ ha hb hd (by omega) z hz hlog hscale hlocal


end LocalLaw
