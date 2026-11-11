import LocalLaw.SharpParameterSmallness

/-! # Realized inversion budgets for a full modified-endpoint benchmark

The reference row cap may grow linearly with the number of endpoints.
The sharper source error bound still realizes contraction and an absolute
new physical error cap, at the original allowed endpoint exponents.
-/

namespace LocalLaw

theorem full_endpoint_log_surgery_budgets (a : ℕ) (L ε n U C0 w D H : ℝ)
    (hL : 1 ≤ L) (hε : 0 ≤ ε) (hn : 0 ≤ n) (hU : 0 ≤ U)
    (hC0 : 0 ≤ C0) (hw : 0 ≤ w) (hD : 0 ≤ D) (hH : 1 ≤ H)
    (hcount : n ≤ U * L ^ (2 * a))
    (hcontract : 2 * U * (1 + U * C0 * w) * w * D ≤ H)
    (herror : 2 * (1 + U * C0 * w) ^ 2 * D ≤ H)
    (hsharp : ε * L ^ (4 * a + 1) ≤ H⁻¹) :
    n * (1 + (n * C0) * w) * w * (D * L * ε) ≤ 1 / 2 ∧
      2 * (1 + (n * C0) * w) ^ 2 * (D * L * ε) ≤ 1 := by
  let P := L ^ (2 * a)
  let M := 1 + U * C0 * w
  have hP : 1 ≤ P := one_le_pow₀ hL
  have hP0 : 0 ≤ P := by linarith
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hrow : 1 + (n * C0) * w ≤ M * P := by
    have hh := mul_le_mul_of_nonneg_right hcount (mul_nonneg hC0 hw)
    change n * (C0 * w) ≤ (U * P) * (C0 * w) at hh
    dsimp only [M]
    nlinarith only [hh, hP]
  have hR0 : 0 ≤ 1 + (n * C0) * w := by positivity
  have hpow : P * P * L = L ^ (4 * a + 1) := by
    dsimp only [P]
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  have hscale0 : 0 ≤ ε * L ^ (4 * a + 1) := mul_nonneg hε (pow_nonneg (by linarith) _)
  have hscaled : H * (ε * L ^ (4 * a + 1)) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hsharp (show 0 ≤ H by linarith)
    simpa only [mul_inv_cancel₀ (show H ≠ 0 by linarith)] using hh
  have hc : n * (1 + (n * C0) * w) * w * (D * L * ε) ≤
      (U * M * w * D) * (ε * L ^ (4 * a + 1)) := by
    calc
      _ ≤ (U * P) * (M * P) * w * (D * L * ε) := by gcongr
      _ = _ := by rw [← hpow]; ring
  have he : 2 * (1 + (n * C0) * w) ^ 2 * (D * L * ε) ≤
      (2 * M ^ 2 * D) * (ε * L ^ (4 * a + 1)) := by
    calc
      _ ≤ 2 * (M * P) ^ 2 * (D * L * ε) := by gcongr
      _ = _ := by rw [← hpow]; ring
  have hcontract' : (2 * U * M * w * D) * (ε * L ^ (4 * a + 1)) ≤ 1 :=
    (mul_le_mul_of_nonneg_right hcontract hscale0).trans hscaled
  have herror' : (2 * M ^ 2 * D) * (ε * L ^ (4 * a + 1)) ≤ 1 :=
    (mul_le_mul_of_nonneg_right herror hscale0).trans hscaled
  exact ⟨by nlinarith only [hc, hcontract'], he.trans herror'⟩

theorem eventually_full_endpoint_surgery_budgets (a b d : ℕ) (β U C0 w D : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hβ : 0 < β)
    (hU : 0 ≤ U) (hC0 : 0 ≤ C0) (hw : 0 ≤ w) (hD : 0 ≤ D) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ, 0 < z.im →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ∀ n : ℝ, 0 ≤ n →
      n ≤ U * Real.log (N : ℝ) ^ (2 * a) →
      let L := Real.log (N : ℝ)
      let ε := paperError a d N (logarithmicRadius β d N) z
        (kestenMcKayTransform d (semicircleRoot z) z).im
      n * (1 + (n * C0) * w) * w * (D * L * ε) ≤ 1 / 2 ∧
        2 * (1 + (n * C0) * w) ^ 2 * (D * L * ε) ≤ 1 := by
  let H := max 1 (max (2 * U * (1 + U * C0 * w) * w * D)
    (2 * (1 + U * C0 * w) ^ 2 * D))
  have hH : 1 ≤ H := le_max_left _ _
  filter_upwards [eventually_paperError_sharp_log_small a b d β H ha hb hd hβ hH,
    eventually_log_ge_nat 1] with N hsharp hL
  intro z hz hfloor n hn hcount
  have hbase := baseError_nonnegative (Real.log (N : ℝ)) a d N (logarithmicRadius β d N)
    z.im (kestenMcKayTransform d (semicircleRoot z) z).im (by linarith) hz.le
  have hε := hbase.trans ((inflateError_bounds (s := spectralScale z) hL hbase).1)
  exact full_endpoint_log_surgery_budgets a _ _ n U C0 w D H hL hε hn hU hC0 hw hD hH hcount
    ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
    (hsharp z hz hfloor)

end LocalLaw
