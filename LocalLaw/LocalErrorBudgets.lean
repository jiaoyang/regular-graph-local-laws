import LocalLaw.ClosureParameters

/-!
# Actual logarithmic gains in the local improvement estimates

The selected interior log-log radius makes (d-1)^(ell/2) at least (log N)^9.
Consequently the explicit epsilon-prime terms in source (4.14)--(4.16) fit
within the row and cavity tolerances used by the constructed closure budget.
Only the graph estimates themselves remain to be supplied.
-/

namespace LocalLaw

noncomputable def resamplingDecayDenominator (d ell : ℕ) : ℝ :=
  Real.sqrt (((d - 1 : ℕ) : ℝ) ^ ell)

theorem selected_radius_power_gain (a d N : ℕ) (z : ℂ)
    (ha : 12 ≤ a) (hd : 3 ≤ d) (hL : 1 ≤ Real.log (N : ℝ)) :
    Real.log (N : ℝ) ^ 18 ≤
      (((d - 1 : ℕ) : ℝ) ^ (actualCavityDepth a d N z - 1)) := by
  let L := Real.log (N : ℝ)
  let k : ℝ := ((d - 1 : ℕ) : ℝ)
  have hk : 1 < k := by dsimp [k]; exact_mod_cast (show 1 < d - 1 by omega)
  have hkp : 0 < k := by linarith
  have hlogk : 0 < Real.log k := Real.log_pos hk
  have hLp : 0 < L := by dsimp [L]; linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hratio : 0 ≤ Real.log L / Real.log k := div_nonneg hlogL hlogk.le
  have haR : (12 : ℝ) ≤ a := Nat.cast_le.mpr ha
  have hstrong := actualCavityDepth_strong_lower a d N z
  have hlower : 18 * Real.log L / Real.log k ≤
      ((actualCavityDepth a d N z - 1 : ℕ) : ℝ) := by
    have hid : (3 / 2 : ℝ) * lowerLogLogRadius a d N =
        (3 / 2 : ℝ) * (a : ℝ) * (Real.log L / Real.log k) := by
      unfold lowerLogLogRadius L k
      ring
    rw [hid] at hstrong
    have haMul := mul_le_mul_of_nonneg_right haR hratio
    calc
      18 * Real.log L / Real.log k = 18 * (Real.log L / Real.log k) := by ring
      _ ≤ (3 / 2 : ℝ) * (a : ℝ) * (Real.log L / Real.log k) := by nlinarith
      _ ≤ _ := hstrong
  have hp := Real.rpow_le_rpow_of_exponent_le hk.le hlower
  have hid : k ^ (18 * Real.log L / Real.log k) = L ^ (18 : ℕ) := by
    rw [Real.rpow_def_of_pos hkp, ← Real.rpow_natCast L 18, Real.rpow_def_of_pos hLp]
    congr 1
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hlogk)]
    norm_num
    ring
  simpa only [hid, Real.rpow_natCast] using hp

theorem selected_radius_decay_gain (a d N : ℕ) (z : ℂ)
    (ha : 12 ≤ a) (hd : 3 ≤ d) (hL : 1 ≤ Real.log (N : ℝ)) :
    Real.log (N : ℝ) ^ 9 ≤
      resamplingDecayDenominator d (actualCavityDepth a d N z - 1) := by
  have hp := Real.sqrt_le_sqrt (selected_radius_power_gain a d N z ha hd hL)
  have heq : Real.log (N : ℝ) ^ 18 = (Real.log (N : ℝ) ^ 9) ^ 2 := by ring
  rw [heq, Real.sqrt_sq (pow_nonneg (by linarith : 0 ≤ Real.log (N : ℝ)) _)] at hp
  exact hp

/-- Exact numerical absorption of source (4.14)--(4.16). D is its common
boundary-decay denominator, not a postulated final error tolerance. -/
theorem local_improvement_error_budgets (L ε C D : ℝ) (hL : 1 ≤ L)
    (hε : 0 ≤ ε) (hC : 0 ≤ C) (hD : L ^ 9 ≤ D) (hconstant : 2 * C ≤ L ^ 3) :
    C * ((L / D + L ^ 2 / D) * inflatedPrime L ε) ≤ ε / L ∧
    C * (L ^ 2 * inflatedPrime L ε / D) ≤ ε / L ∧
    C * (L * inflatedPrime L ε / D) ≤ ε / (2 * L ^ 2) := by
  have hLp : 0 < L := by linarith
  have hDp : 0 < D := (pow_pos hLp 9).trans_le hD
  have hcRatio : C / L ^ 3 ≤ 1 / 2 := by
    apply (div_le_iff₀ (pow_pos hLp 3)).mpr
    linarith
  have htwo : 2 * C / L ^ 3 ≤ 1 := by
    exact (div_le_one (pow_pos hLp 3)).mpr hconstant
  have hfive : L ^ 5 * ε / D ≤ ε / L ^ 4 := by
    calc
      L ^ 5 * ε / D ≤ L ^ 5 * ε / L ^ 9 :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hLp 9) hD
      _ = ε / L ^ 4 := by field_simp [ne_of_gt hLp]; ring
  have hfour : L ^ 4 * ε / D ≤ ε / L ^ 5 := by
    calc
      L ^ 4 * ε / D ≤ L ^ 4 * ε / L ^ 9 :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hLp 9) hD
      _ = ε / L ^ 5 := by field_simp [ne_of_gt hLp]; ring
  have hout : C * (L ^ 2 * inflatedPrime L ε / D) ≤ ε / L := by
    calc
      C * (L ^ 2 * inflatedPrime L ε / D) = C * (L ^ 5 * ε / D) := by
        unfold inflatedPrime
        ring
      _ ≤ C * (ε / L ^ 4) := mul_le_mul_of_nonneg_left hfive hC
      _ = (C / L ^ 3) * (ε / L) := by simp only [div_eq_mul_inv, inv_pow]; ring
      _ ≤ (1 / 2) * (ε / L) := mul_le_mul_of_nonneg_right hcRatio (by positivity)
      _ ≤ ε / L := by nlinarith [div_nonneg hε hLp.le]
  refine ⟨?_, hout, ?_⟩
  · have hp : L ^ 4 ≤ L ^ 5 := pow_le_pow_right₀ hL (by omega)
    have hn : (L / D + L ^ 2 / D) * inflatedPrime L ε ≤ 2 * (L ^ 5 * ε / D) := by
      have hh := mul_le_mul_of_nonneg_right hp hε
      calc
        _ = (L ^ 4 * ε + L ^ 5 * ε) / D := by unfold inflatedPrime; ring
        _ ≤ (2 * (L ^ 5 * ε)) / D :=
          div_le_div_of_nonneg_right (by linarith) hDp.le
        _ = _ := by ring
    calc
      C * ((L / D + L ^ 2 / D) * inflatedPrime L ε) ≤ C * (2 * (L ^ 5 * ε / D)) :=
        mul_le_mul_of_nonneg_left hn hC
      _ ≤ 2 * C * (ε / L ^ 4) := by nlinarith [mul_le_mul_of_nonneg_left hfive hC]
      _ = (2 * C / L ^ 3) * (ε / L) := by simp only [div_eq_mul_inv, inv_pow]; ring
      _ ≤ 1 * (ε / L) := mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = ε / L := one_mul _
  · calc
      C * (L * inflatedPrime L ε / D) = C * (L ^ 4 * ε / D) := by
        unfold inflatedPrime
        ring
      _ ≤ C * (ε / L ^ 5) := mul_le_mul_of_nonneg_left hfour hC
      _ = (C / L ^ 3) * (ε / L ^ 2) := by simp only [div_eq_mul_inv, inv_pow]; ring
      _ ≤ (1 / 2) * (ε / L ^ 2) := mul_le_mul_of_nonneg_right hcRatio (by positivity)
      _ = ε / (2 * L ^ 2) := by ring

end LocalLaw
