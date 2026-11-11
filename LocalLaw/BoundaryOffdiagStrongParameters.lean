import LocalLaw.BoundaryOffdiagParameters

/-! # The paired good off-diagonal forcing also fits four inverse logs -/

namespace LocalLaw

theorem paired_weighted_good_strong_absorption (a : ℕ) (L ε n δ φ U D G W : ℝ)
    (ha : 12 ≤ a) (hL : 1 ≤ L) (hε : 0 ≤ ε) (hn : 0 ≤ n) (hδ : 0 ≤ δ) (hφ : 0 ≤ φ)
    (hU : 0 ≤ U) (hD : 0 ≤ D) (hG : 0 ≤ G) (hW : 0 ≤ W)
    (hcap : ε * L ^ (4 * a) ≤ 1) (hcount : n ≤ U * L ^ (2 * a))
    (herror : δ ≤ D * L ^ 3 * ε) (hcorr : φ * L ^ (4 * a) ≤ ε)
    (hlarge1 : 3 * G * U * W * D ^ 2 ≤ L)
    (hlarge2 : 3 * G * U ^ 2 * W * D ≤ L)
    (hlarge3 : 3 * G * U * W ≤ L) :
    (G * (δ ^ 2 + n * φ * δ + φ)) * (n * W * L) ≤ ε / L ^ 4 := by
  have hLp : 0 < L := by linarith
  have hL0 := hLp.le
  have hnSquare : n ^ 2 ≤ U ^ 2 * L ^ (4 * a) := by
    apply (pow_le_pow_left₀ hn hcount 2).trans_eq
    rw [mul_pow, ← pow_mul]
    congr 2
    omega
  have hnPhi : n ^ 2 * φ ≤ U ^ 2 * ε := by
    calc
      _ ≤ (U ^ 2 * L ^ (4 * a)) * φ := mul_le_mul_of_nonneg_right hnSquare hφ
      _ = U ^ 2 * (φ * L ^ (4 * a)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcorr (sq_nonneg U)
  have hfirst : 3 * G * δ ^ 2 * (n * W * L) ≤ ε / L ^ 4 := by
    calc
      _ ≤ 3 * G * (D * L ^ 3 * ε) ^ 2 * ((U * L ^ (2 * a)) * W * L) := by
        gcongr
      _ = (3 * G * U * W * D ^ 2) * ε ^ 2 * L ^ (2 * a + 7) := by rw [pow_add]; ring
      _ ≤ _ := source_squared_error_log_absorption a (2 * a + 7) 4 L ε
        (3 * G * U * W * D ^ 2) hL hε (by positivity) hcap (by omega) hlarge1
  have hsecond : 3 * G * (n * φ * δ) * (n * W * L) ≤ ε / L ^ 4 := by
    calc
      _ = 3 * G * (n ^ 2 * φ) * δ * W * L := by ring
      _ ≤ 3 * G * (U ^ 2 * ε) * (D * L ^ 3 * ε) * W * L := by gcongr
      _ = (3 * G * U ^ 2 * W * D) * ε ^ 2 * L ^ 4 := by ring
      _ ≤ _ := source_squared_error_log_absorption a 4 4 L ε
        (3 * G * U ^ 2 * W * D) hL hε (by positivity) hcap (by omega) hlarge2
  have hthird : 3 * G * φ * (n * W * L) ≤ ε / L ^ 4 := by
    apply (le_div_iff₀ (pow_pos hLp 4)).mpr
    calc
      _ = (3 * G * φ * W * L) * n * L ^ 4 := by ring
      _ ≤ (3 * G * φ * W * L) * (U * L ^ (2 * a)) * L ^ 4 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcount (by positivity)) (pow_nonneg hL0 4)
      _ = (3 * G * U * W) * φ * L ^ (2 * a + 5) := by rw [pow_add]; ring
      _ ≤ L * φ * L ^ (2 * a + 5) := by gcongr
      _ = φ * L ^ (2 * a + 6) := by rw [show 2*a+6=(2*a+5)+1 by omega, pow_succ]; ring
      _ ≤ φ * L ^ (4 * a) := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega)) hφ
      _ ≤ _ := hcorr
  nlinarith only [hfirst, hsecond, hthird]

end LocalLaw
