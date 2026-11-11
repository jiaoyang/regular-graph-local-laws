import LocalLaw.ParameterSmallness

/-! # The additional logarithmic slack in the source sample floor

The allowed endpoint a=12, b=25a still gives epsilon*L^(4a+1) tending
uniformly to zero. No corresponding vanishing claim at exponent 4a+2 is
made. This is the scale needed for a full modified-endpoint block with
O(L^(2a)) vertices and an O(L*epsilon) common-model error.
-/

open Filter
namespace LocalLaw

private theorem sharp_variance_component (I X P : ℝ) (hI : I ≤ 2)
    (hP : 0 < P) (hX : 18 * P ^ 2 ≤ X) :
    Real.sqrt (I / X) ≤ 1 / (3 * P) := by
  have hXp : 0 < X := lt_of_lt_of_le (by positivity) hX
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    I / X ≤ 2 / X := div_le_div_of_nonneg_right hI hXp.le
    _ ≤ 2 / (18 * P ^ 2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hX
    _ = (1 / (3 * P)) ^ 2 := by field_simp; ring

private theorem sharp_fractional_component (X P : ℝ) (hP : 1 ≤ P)
    (hX : 18 * P ^ 2 ≤ X) :
    (X ^ (2 / 3 : ℝ))⁻¹ ≤ 1 / (3 * P) := by
  have hPp : 0 < P := by linarith
  have hXone : 1 ≤ X := by nlinarith
  have hsqrt : 3 * P ≤ Real.sqrt X := by
    have hs := Real.sqrt_le_sqrt (show (3 * P) ^ 2 ≤ X by nlinarith)
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < 3 * P)] at hs
    exact hs
  have hp := Real.rpow_le_rpow_of_exponent_le hXone (by norm_num : (1 / 2 : ℝ) ≤ 2 / 3)
  have hden : 3 * P ≤ X ^ (2 / 3 : ℝ) := hsqrt.trans
    (by simpa only [Real.sqrt_eq_rpow] using hp)
  simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < 3 * P) hden

theorem paperError_sharp_log_small_of_radius_budget (a b d N r : ℕ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hN : 0 < N)
    (M : ℝ) (hM : 1 ≤ M) (z : ℂ) (hz : 0 < z.im)
    (hL : 3 ≤ Real.log (N : ℝ))
    (hLM : 18 * M ^ 2 + M ≤ Real.log (N : ℝ))
    (hscale : Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im)
    (hlocal : (((d - 1 : ℕ) : ℝ) ^ r)⁻¹ ≤
      1 / (3 * Real.log (N : ℝ) ^ (12 * a + 6))) :
    paperError a d N r z (kestenMcKayTransform d (semicircleRoot z) z).im *
      Real.log (N : ℝ) ^ (4 * a + 1) ≤ M⁻¹ := by
  let L := Real.log (N : ℝ)
  let P := M * L ^ (12 * a + 5)
  let X := (N : ℝ) * z.im
  have hLone : 1 ≤ L := by dsimp only [L]; linarith
  have hLp : 0 < L := by linarith
  have hMp : 0 < M := by linarith
  have hPone : 1 ≤ P := one_le_mul_of_one_le_of_one_le hM (one_le_pow₀ hLone)
  have hPp : 0 < P := by linarith
  have hXraw : L ^ b ≤ X := by
    have h := (div_le_iff₀ (Nat.cast_pos.mpr hN : (0 : ℝ) < N)).mp hscale
    simpa only [L, X, mul_comm] using h
  have hMlarge : 18 * M ^ 2 ≤ L ^ 2 := by
    have h1 : 18 * M ^ 2 ≤ L := by dsimp only [L]; nlinarith only [hLM, hM]
    have h2 : L ≤ L ^ 2 := by nlinarith only [hLone]
    exact h1.trans h2
  have hlarge : 18 * P ^ 2 ≤ X := by
    calc
      _ = (18 * M ^ 2) * L ^ (2 * (12 * a + 5)) := by dsimp only [P]; rw [mul_pow, pow_mul]; ring
      _ ≤ L ^ 2 * L ^ (2 * (12 * a + 5)) :=
        mul_le_mul_of_nonneg_right hMlarge (pow_nonneg hLp.le _)
      _ = L ^ (2 + 2 * (12 * a + 5)) := (pow_add ..).symm
      _ ≤ L ^ b := pow_le_pow_right₀ hLone (by omega)
      _ ≤ X := hXraw
  have hIm : (kestenMcKayTransform d (semicircleRoot z) z).im ≤ 2 :=
    ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (kestenMcKayTransform_norm_le_two d hd z hz)
  have hvar := sharp_variance_component _ X P hIm hPp hlarge
  have hfrac := sharp_fractional_component X P hPone hlarge
  have hloc : (((d - 1 : ℕ) : ℝ) ^ r)⁻¹ ≤ 1 / (3 * P) := by
    apply hlocal.trans
    apply one_div_le_one_div_of_le (by positivity : 0 < 3 * P)
    have hML : M ≤ L := by dsimp only [L]; nlinarith only [hLM, sq_nonneg M]
    change 3 * (M * L ^ (12 * a + 5)) ≤ 3 * L ^ (12 * a + 6)
    have hpows : L ^ (12 * a + 6) = L * L ^ (12 * a + 5) := by
      convert pow_succ' L (12 * a + 5) using 1
    rw [hpows]
    nlinarith only [mul_le_mul_of_nonneg_right hML (pow_nonneg hLp.le (12 * a + 5))]
  have hterms : baseErrorTerms d N r z.im
      (kestenMcKayTransform d (semicircleRoot z) z).im ≤ P⁻¹ := by
    change (((d - 1 : ℕ) : ℝ) ^ r)⁻¹ +
      Real.sqrt ((kestenMcKayTransform d (semicircleRoot z) z).im / X) +
        (X ^ (2 / 3 : ℝ))⁻¹ ≤ P⁻¹
    calc
      _ ≤ 1 / (3 * P) + 1 / (3 * P) + 1 / (3 * P) := add_le_add (add_le_add hloc hvar) hfrac
      _ = P⁻¹ := by field_simp [ne_of_gt hPp]; ring
  have hinflate := (inflateError_bounds (s := spectralScale z) hLone
    (baseError_nonnegative L a d N r z.im (kestenMcKayTransform d (semicircleRoot z) z).im hLp.le hz.le)).2
  change inflateError L (baseError L a d N r z.im (kestenMcKayTransform d (semicircleRoot z) z).im)
    (spectralScale z) * L ^ (4 * a + 1) ≤ M⁻¹
  calc
    _ ≤ (L ^ 4 * baseError L a d N r z.im _) * L ^ (4 * a + 1) :=
      mul_le_mul_of_nonneg_right hinflate (pow_nonneg hLp.le _)
    _ ≤ (L ^ 4 * (L ^ (8 * a) * P⁻¹)) * L ^ (4 * a + 1) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hLp.le _)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hterms (pow_nonneg hLp.le _))
        (pow_nonneg hLp.le _)
    _ = M⁻¹ := by
      dsimp only [P]
      rw [show 12 * a + 5 = (4 + 8 * a) + (4 * a + 1) by omega, pow_add, pow_add]
      field_simp [ne_of_gt hMp, ne_of_gt hLp]
      ring

theorem eventually_paperError_sharp_log_small (a b d : ℕ) (β M : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hβ : 0 < β) (hM : 1 ≤ M) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 < z.im →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      paperError a d N (logarithmicRadius β d N) z
          (kestenMcKayTransform d (semicircleRoot z) z).im *
        Real.log (N : ℝ) ^ (4 * a + 1) ≤ M⁻¹ := by
  filter_upwards [eventually_localization_log_budget β d (12 * a + 6) hβ hd,
    eventually_log_ge_nat 3, eventually_log_ge_nat (18 * M ^ 2 + M),
    eventually_ge_atTop 1] with N hlocal hlog hMlog hN
  intro z hz hscale
  exact paperError_sharp_log_small_of_radius_budget a b d N _ ha hb hd (by omega)
    M hM z hz hlog hMlog hscale hlocal

end LocalLaw
