import LocalLaw.GoodWeightedDiagonalParameters

/-! # Retain the fourth-log forcing rate with its explicit fixed constant -/

namespace LocalLaw

theorem good_weighted_diagonal_strong_budget (L ε Cnoise Cobs A Bbad W D : ℝ)
    (hL : 1 ≤ L) (hε : 0 ≤ ε) (hnoise : 0 ≤ Cnoise) (hobs : 0 ≤ Cobs)
    (hA : 0 ≤ A) (hbad : 0 ≤ Bbad) (hW : 0 ≤ W) (hD : L ^ 9 ≤ D) :
    Cnoise * L ^ 2 * (Cobs * inflatedPrime L ε) / D +
        (3 * ε / L ^ 16) * A * L + (ε / L ^ 16) * A * L +
        (2 * (Cobs * inflatedPrime L ε) + 3 * ε / L ^ 16) *
          (Bbad * L ^ 2) * (W / D) ≤
        (Cnoise * Cobs + 4 * A + (2 * Cobs + 3) * Bbad * W) * (ε / L ^ 4) := by
  have hLp : 0 < L := by linarith
  have hDp : 0 < D := (pow_pos hLp 9).trans_le hD
  have hdecay : L ^ 5 * ε / D ≤ ε / L ^ 4 := by
    calc
      _ ≤ L ^ 5 * ε / L ^ 9 := div_le_div_of_nonneg_left (by positivity) (pow_pos hLp 9) hD
      _ = _ := by field_simp [ne_of_gt hLp]; ring
  have hsmall : ε / L ^ 16 * L ≤ ε / L ^ 4 := by
    have hh := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left hε (pow_pos hLp 5)
        (pow_le_pow_right₀ hL (by norm_num : 5 ≤ 16))) hLp.le
    exact hh.trans_eq (by field_simp [ne_of_gt hLp]; ring)
  have hnoiseBound : Cnoise * L ^ 2 * (Cobs * inflatedPrime L ε) / D ≤
      (Cnoise * Cobs) * (ε / L ^ 4) := by
    calc
      _ = (Cnoise * Cobs) * (L ^ 5 * ε / D) := by unfold inflatedPrime; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (mul_nonneg hnoise hobs)
  have hsmallBound : (3 * ε / L ^ 16) * A * L + (ε / L ^ 16) * A * L ≤
      (4 * A) * (ε / L ^ 4) := by
    have hh := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 4 * A by positivity)
    convert hh using 1; ring
  have hobsBound : 2 * (Cobs * inflatedPrime L ε) + 3 * ε / L ^ 16 ≤
      (2 * Cobs + 3) * L ^ 3 * ε := by
    have hh : ε / L ^ 16 ≤ L ^ 3 * ε :=
      (div_le_self hε (one_le_pow₀ hL)).trans
        (by nlinarith [mul_le_mul_of_nonneg_right (show 1 ≤ L ^ 3 from one_le_pow₀ hL) hε])
    calc
      _ = 2 * (Cobs * L ^ 3 * ε) + 3 * (ε / L ^ 16) := by unfold inflatedPrime; ring
      _ ≤ 2 * (Cobs * L ^ 3 * ε) + 3 * (L ^ 3 * ε) :=
        add_le_add_left (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 3)) _
      _ = _ := by ring
  have hbadBound : (2 * (Cobs * inflatedPrime L ε) + 3 * ε / L ^ 16) *
      (Bbad * L ^ 2) * (W / D) ≤ ((2 * Cobs + 3) * Bbad * W) * (ε / L ^ 4) := by
    calc
      _ ≤ ((2 * Cobs + 3) * L ^ 3 * ε) * (Bbad * L ^ 2) * (W / D) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hobsBound (by positivity)) (by positivity)
      _ = ((2 * Cobs + 3) * Bbad * W) * (L ^ 5 * ε / D) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)
  calc
    _ ≤ ((Cnoise * Cobs) + 4 * A + (2 * Cobs + 3) * Bbad * W) * (ε / L ^ 4) := by
      linarith only [hnoiseBound, hsmallBound, hbadBound]

theorem eventually_actual_good_weighted_diagonal_strong_budget (a d : ℕ)
    (Cnoise Cobs A Bbad W : ℝ) (ha : 12 ≤ a) (hd : 3 ≤ d)
    (hnoise : 0 ≤ Cnoise) (hobs : 0 ≤ Cobs) (hA : 0 ≤ A)
    (hbad : 0 ≤ Bbad) (hW : 0 ≤ W) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (rError : ℕ) (z : ℂ), 0 ≤ z.im →
      let L := Real.log (N : ℝ)
      let ε := graphPaperError a d N rError z
      let D := resamplingDecayDenominator d (actualCavityDepth a d N z - 1)
      Cnoise * L ^ 2 * (Cobs * inflatedPrime L ε) / D +
          (3 * ε / L ^ 16) * A * L + (ε / L ^ 16) * A * L +
          (2 * (Cobs * inflatedPrime L ε) + 3 * ε / L ^ 16) *
            (Bbad * L ^ 2) * (W / D) ≤
        (Cnoise * Cobs + 4 * A + (2 * Cobs + 3) * Bbad * W) * (ε / L ^ 4) := by
  filter_upwards [eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1] with N hlog hN
  intro rError z hz
  dsimp only
  exact good_weighted_diagonal_strong_budget _ _ Cnoise Cobs A Bbad W _ hlog
    (graphPaperError_nonnegative a d N rError z hN hz) hnoise hobs hA hbad hW
    (selected_radius_decay_gain a d N z ha hd hlog)

end LocalLaw
