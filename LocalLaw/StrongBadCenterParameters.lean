import LocalLaw.BadCenterAsymptotics
import LocalLaw.MomentTailParameters

/-!
# All numerical budgets for a strong bad-center moment tail

The moment order, shared sparse-pattern budget, greedy-packing threshold and
polynomial tail factor are realized at the actual structural radius. The
finite combinatorial packing-to-event theorem remains a separate proof.
-/

namespace LocalLaw

noncomputable def badCenterMomentNumerator (d R : ℕ) : ℕ :=
  2 * (d + 1) * (2 * R + 2) ^ 2 * (d - 1) ^ (3 * R + 1)

/-- A fixed power gap gamma-3c/4 suffices for every desired probability
exponent, with no remaining numerical hypotheses on N. -/
theorem eventually_strong_badCenter_budgets (d ω p : ℕ) (c γ : ℝ) (hd : 3 ≤ d)
    (hc : 0 ≤ c) (hγ : 3 * c / 4 < γ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      let R := logarithmicRadius (c / 4) d N
      let q := sufficientMomentOrder (γ - 3 * c / 4) p
      let K := q * (2 * R + 1)
      0 < N ∧ 1 ≤ q ∧
      2 * K * RegularGraph.patternSwitchSlack d K ≤ N * d ∧
      ((q * 2 ^ ω * badCenterMomentNumerator d R : ℕ) : ℝ) ≤ (N : ℝ) ^ γ ∧
      2 * ((badCenterMomentNumerator d R : ℝ) / (N : ℝ) ^ γ) ^ q ≤ 1 / (N : ℝ) ^ p := by
  let gap := γ - 3 * c / 4
  let q := sufficientMomentOrder gap p
  let C := badCenterMomentConstant d c
  let ρ := structuralRadiusCoefficient d c
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hk : (1 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < d - 1 by omega)
  have hρ : 0 ≤ ρ := div_nonneg (by positivity) (Real.log_pos hk).le
  have hC : 0 ≤ C := by dsimp [C, badCenterMomentConstant]; positivity
  have hqbound := sufficientMomentOrder_bound gap p hgap
  have hqpos : 1 ≤ q := by
    by_contra hnot
    have hzero : q = 0 := by omega
    change ((p + 1 : ℕ) : ℝ) ≤ (q : ℝ) * gap / 2 at hqbound
    rw [hzero] at hqbound
    have hp : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    norm_num at hqbound
    linarith
  have hbudget := eventually_pattern_switching_budget d (2 * (q : ℝ) * ρ) (q : ℝ)
    (by omega) (by positivity) (Nat.cast_nonneg _)
  have hthreshold := eventually_const_mul_log_rpow_le
    (((q * 2 ^ ω : ℕ) : ℝ) * C) 2 gap hgap
  have htail := eventually_chosen_moment_decay C gap 2 p hC hgap
  filter_upwards [hbudget, hthreshold, htail, eventually_log_ge_nat 1,
    Filter.eventually_ge_atTop 1] with N hbudget hthreshold htail hlog hN
  let R := logarithmicRadius (c / 4) d N
  let K := q * (2 * R + 1)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNgap : 0 < (N : ℝ) ^ gap := Real.rpow_pos_of_pos hn _
  have hNc : 0 < (N : ℝ) ^ (3 * c / 4) := Real.rpow_pos_of_pos hn _
  have hNgamma : 0 < (N : ℝ) ^ γ := Real.rpow_pos_of_pos hn _
  have hnum := badCenter_numerator_bound d N c hd hc hN hlog
  change (badCenterMomentNumerator d R : ℝ) ≤ C * Real.log (N : ℝ) ^ 2 * (N : ℝ) ^ (3 * c / 4) at hnum
  have hr := structuralRadius_le_log d N c hd hc hN
  change (R : ℝ) ≤ ρ * Real.log (N : ℝ) at hr
  have hK : (K : ℝ) ≤ (2 * (q : ℝ) * ρ) * Real.log (N : ℝ) + q := by
    have h := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    dsimp [K]
    push_cast
    nlinarith
  have hcombine : (N : ℝ) ^ gap * (N : ℝ) ^ (3 * c / 4) = (N : ℝ) ^ γ := by
    rw [← Real.rpow_add hn]
    congr 1
    dsimp [gap]
    ring
  have hthreshold' : (((q * 2 ^ ω : ℕ) : ℝ) * C) * Real.log (N : ℝ) ^ 2 ≤ (N : ℝ) ^ gap := by
    simpa only [Real.rpow_two] using hthreshold
  have hcount : ((q * 2 ^ ω * badCenterMomentNumerator d R : ℕ) : ℝ) ≤ (N : ℝ) ^ γ := by
    calc
      _ = (((q * 2 ^ ω : ℕ) : ℝ)) * (badCenterMomentNumerator d R : ℝ) := by push_cast; ring
      _ ≤ (((q * 2 ^ ω : ℕ) : ℝ)) * (C * Real.log (N : ℝ) ^ 2 * (N : ℝ) ^ (3 * c / 4)) :=
        mul_le_mul_of_nonneg_left hnum (Nat.cast_nonneg _)
      _ = ((((q * 2 ^ ω : ℕ) : ℝ)) * C * Real.log (N : ℝ) ^ 2) * (N : ℝ) ^ (3 * c / 4) := by ring
      _ ≤ (N : ℝ) ^ gap * (N : ℝ) ^ (3 * c / 4) := mul_le_mul_of_nonneg_right hthreshold' hNc.le
      _ = _ := hcombine
  have hratio : (badCenterMomentNumerator d R : ℝ) / (N : ℝ) ^ γ ≤
      C * Real.log (N : ℝ) ^ 2 / (N : ℝ) ^ gap := by
    calc
      _ ≤ (C * Real.log (N : ℝ) ^ 2 * (N : ℝ) ^ (3 * c / 4)) / (N : ℝ) ^ γ :=
        div_le_div_of_nonneg_right hnum hNgamma.le
      _ = _ := by
        rw [← hcombine]
        field_simp [ne_of_gt hNgap, ne_of_gt hNc]
        ring
  refine ⟨by omega, hqpos, hbudget K hK, hcount, ?_⟩
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ (badCenterMomentNumerator d R : ℝ) / (N : ℝ) ^ γ by positivity)
    hratio q
  exact (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)).trans htail

end LocalLaw
