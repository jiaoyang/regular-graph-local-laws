import LocalLaw.SourceObservationParameters
import LocalLaw.SharpSamplingCounts

/-!
# Source logarithmic gains for endpoint surgery

The actual nominal error makes finite-rank inversion small and absorbs the
squared-error and correlation-density corrections. All estimates retain the
nominal error radius rather than comparing inflation branches.
-/

namespace LocalLaw

theorem source_scaled_log_monomial_half (a p : ℕ) (L ε H : ℝ)
    (hL : 1 ≤ L) (hε : 0 ≤ ε) (hH : 0 ≤ H)
    (hcap : ε * L ^ (4 * a) ≤ 1) (hp : p + 1 ≤ 4 * a) (hlarge : 2 * H ≤ L) :
    H * ε * L ^ p ≤ 1 / 2 := by
  have hLp : 0 < L := by linarith
  have hscale := (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hp) hε).trans hcap
  apply (mul_le_mul_right hLp).mp
  have hh := mul_le_mul_of_nonneg_left hscale hH
  rw [pow_succ] at hh
  have hterm : (H * ε * L ^ p) * L ≤ H := by nlinarith only [hh]
  exact hterm.trans (by linarith only [hlarge])

/-- The literal endpoint dimension times surgery error is small. -/
theorem source_endpoint_surgery_smallness (a : ℕ) (L ε n U C w D : ℝ)
    (ha : 2 ≤ a) (hL : 1 ≤ L) (hε : 0 ≤ ε)
    (hU : 0 ≤ U) (hC : 0 ≤ C) (hw : 0 ≤ w) (hD : 0 ≤ D)
    (hcap : ε * L ^ (4 * a) ≤ 1) (hcount : n ≤ U * L ^ (2 * a))
    (hlarge : 2 * (U * (1 + C * w) * w * D) ≤ L) :
    n * (1 + C * w) * w * (D * L ^ 3 * ε) ≤ 1 / 2 := by
  have hnonneg : 0 ≤ (1 + C * w) * w * (D * L ^ 3 * ε) := by positivity
  calc
    _ = n * ((1 + C * w) * w * (D * L ^ 3 * ε)) := by ring
    _ ≤ (U * L ^ (2 * a)) * ((1 + C * w) * w * (D * L ^ 3 * ε)) :=
      mul_le_mul_of_nonneg_right hcount hnonneg
    _ = (U * (1 + C * w) * w * D) * ε * L ^ (2 * a + 3) := by rw [pow_add]; ring
    _ ≤ 1 / 2 := source_scaled_log_monomial_half a (2 * a + 3) L ε
      (U * (1 + C * w) * w * D) hL hε (by positivity) hcap (by omega) hlarge

/-- A second copy of the small source error buys any fixed remaining
logarithmic tolerance within the explicit exponent budget. -/
theorem source_squared_error_log_absorption (a p q : ℕ) (L ε H : ℝ)
    (hL : 1 ≤ L) (hε : 0 ≤ ε) (_hH : 0 ≤ H)
    (hcap : ε * L ^ (4 * a) ≤ 1) (hpq : p + q + 1 ≤ 4 * a) (hlarge : H ≤ L) :
    H * ε ^ 2 * L ^ p ≤ ε / L ^ q := by
  have hLp : 0 < L := by linarith
  have hscale := (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hpq) hε).trans hcap
  apply (le_div_iff₀ (pow_pos hLp q)).mpr
  calc
    _ = H * ε ^ 2 * L ^ (p + q) := by rw [pow_add]; ring
    _ ≤ L * ε ^ 2 * L ^ (p + q) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlarge (sq_nonneg ε)) (by positivity)
    _ = ε * (ε * L ^ (p + q + 1)) := by rw [pow_succ]; ring
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hscale hε
    _ = _ := mul_one _

/-- Squared endpoint errors and the entire correlation-density cost both
fit sixteen inverse logarithms when a>=12. -/
theorem source_surgery_diagonal_correction_absorption (a : ℕ) (L ε n U D K φ : ℝ)
    (ha : 12 ≤ a) (hL : 1 ≤ L) (hε : 0 ≤ ε) (hn : 0 ≤ n)
    (_hU : 0 ≤ U) (_hD : 0 ≤ D) (hK : 0 ≤ K)
    (hcap : ε * L ^ (4 * a) ≤ 1) (hcount : n ≤ U * L ^ (2 * a))
    (hφ : φ ≤ ε / L ^ (4 * a))
    (hlargeSquare : 2 * K * D ^ 2 ≤ L) (hlargeDensity : 2 * K * U ≤ L) :
    K * ((D * L ^ 3 * ε) ^ 2 + n * φ) ≤ ε / L ^ 16 := by
  have hLp : 0 < L := by linarith
  have hL0 : 0 ≤ L := hLp.le
  have hφcap : 0 ≤ ε / L ^ (4 * a) := by positivity
  have hfirst : (2 * K) * (D * L ^ 3 * ε) ^ 2 ≤ ε / L ^ 16 := by
    have hh := source_squared_error_log_absorption a 6 16 L ε (2 * K * D ^ 2)
      hL hε (by positivity) hcap (by omega) hlargeSquare
    exact (by ring_nf at hh ⊢; exact hh)
  have hsecond : (2 * K) * n * φ ≤ ε / L ^ 16 := by
    have hh : (2 * K) * n * φ ≤ (2 * K * U) * ε * L ^ (2 * a) / L ^ (4 * a) := by
      calc
        _ ≤ (2 * K) * n * (ε / L ^ (4 * a)) := mul_le_mul_of_nonneg_left hφ (by positivity)
        _ ≤ (2 * K) * (U * L ^ (2 * a)) * (ε / L ^ (4 * a)) := by gcongr
        _ = _ := by ring
    apply hh.trans
    apply (div_le_iff₀ (pow_pos hLp (4 * a))).mpr
    apply (mul_le_mul_right (pow_pos hLp 16)).mp
    have hexp : (2 * a + 17) ≤ 4 * a := by omega
    calc
      _ = (2 * K * U) * ε * L ^ (2 * a + 16) := by rw [pow_add]; ring
      _ ≤ L * ε * L ^ (2 * a + 16) := by gcongr
      _ = ε * L ^ (2 * a + 17) := by rw [pow_succ]; ring
      _ ≤ ε * L ^ (4 * a) := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hexp) hε
      _ = _ := by field_simp
  have hh := add_le_add hfirst hsecond
  have hsum : 2 * (K * ((D * L ^ 3 * ε) ^ 2 + n * φ)) ≤ 2 * (ε / L ^ 16) := by nlinarith only [hh]
  linarith only [hsum]

end LocalLaw
