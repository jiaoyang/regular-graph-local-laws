import LocalLaw.UniversalBadCenterMoments
import LocalLaw.MomentTailParameters

/-! # Actual uniform bad-center moments at any fixed radius offset -/

namespace LocalLaw

noncomputable def universalBadCenterConstant (d J : ℕ) (c : ℝ) : ℝ :=
  2 * ((d : ℝ) + 1) ^ 2 *
    (2 * structuralRadiusCoefficient d c + 2 * (J : ℝ) + 2) ^ 3 *
    (((d - 1 : ℕ) : ℝ) ^ (3 * J + 1))

/-- A fixed additive radius offset changes only the finite constant. -/
theorem universal_badCenter_numerator_bound (d N J : ℕ) (c : ℝ)
    (hd : 3 ≤ d) (hc : 0 ≤ c) (hN : 1 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ)) :
    let R := logarithmicRadius (c / 4) d N + J
    (universalBadCenterNumerator d R : ℝ) ≤
      universalBadCenterConstant d J c * Real.log (N : ℝ) ^ 3 * (N : ℝ) ^ (3 * c / 4) := by
  let R := logarithmicRadius (c / 4) d N
  let ρ := structuralRadiusCoefficient d c
  let k : ℝ := ((d - 1 : ℕ) : ℝ)
  have hk : 1 < k := by dsimp [k]; exact_mod_cast (show 1 < d - 1 by omega)
  have hkp : 0 < k := by linarith
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hρ : 0 ≤ ρ := div_nonneg (by positivity) (Real.log_pos hk).le
  have hr := structuralRadius_le_log d N c hd hc hN
  change (R : ℝ) ≤ ρ * Real.log (N : ℝ) at hr
  have hlinear : 2 * ((R : ℝ) + J) + 2 ≤ (2 * ρ + 2 * (J : ℝ) + 2) * Real.log (N : ℝ) := by nlinarith
  have hpoly := pow_le_pow_left₀ (show 0 ≤ 2 * ((R : ℝ) + J) + 2 by positivity) hlinear 3
  have hp : k ^ R ≤ (N : ℝ) ^ (c / 4) := logarithmicRadius_power_bound (c / 4) d N (by positivity) hd hN
  have hcube := pow_le_pow_left₀ (pow_nonneg hkp.le R) hp 3
  have hNpower : ((N : ℝ) ^ (c / 4)) ^ (3 : ℕ) = (N : ℝ) ^ (3 * c / 4) := by
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hn.le]
    congr 1
    ring
  rw [hNpower] at hcube
  have hpower : k ^ (3 * (R + J) + 1) ≤ k ^ (3 * J + 1) * (N : ℝ) ^ (3 * c / 4) := by
    calc
      _ = k ^ (3 * J + 1) * (k ^ R) ^ 3 := by
        rw [show 3 * (R + J) + 1 = R * 3 + (3 * J + 1) by omega, pow_add, pow_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcube (pow_nonneg hkp.le _)
  have hprod := mul_le_mul hpoly hpower (pow_nonneg hkp.le _) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2 * ((d : ℝ) + 1) ^ 2 by positivity)
  dsimp only [universalBadCenterNumerator]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] at hscaled ⊢
  convert hscaled using 1
  all_goals
    dsimp only [universalBadCenterConstant, ρ, k, R]
    ring

/-- The actual moment order, switching budget, packing threshold, and tail
budget hold eventually at R=floor((c/4)log_k N)+J. -/
theorem eventually_universal_badCenter_budgets (d J p : ℕ) (c γ : ℝ)
    (hd : 3 ≤ d) (hc : 0 ≤ c) (hγ : 3 * c / 4 < γ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      let R := logarithmicRadius (c / 4) d N + J
      let q := sufficientMomentOrder (γ - 3 * c / 4) p
      let K := q * (2 * R + 1)
      0 < N ∧ 1 ≤ q ∧ 2 * K * RegularGraph.patternSwitchSlack d K ≤ N * d ∧
      ((q * universalBadCenterNumerator d R : ℕ) : ℝ) ≤ (N : ℝ) ^ γ ∧
      2 * ((universalBadCenterNumerator d R : ℝ) / (N : ℝ) ^ γ) ^ q ≤ 1 / (N : ℝ) ^ p := by
  let gap := γ - 3 * c / 4
  let q := sufficientMomentOrder gap p
  let C := universalBadCenterConstant d J c
  let ρ := structuralRadiusCoefficient d c
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hk : (1 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < d - 1 by omega)
  have hρ : 0 ≤ ρ := div_nonneg (by positivity) (Real.log_pos hk).le
  have hC : 0 ≤ C := by dsimp [C, universalBadCenterConstant]; positivity
  have hqbound := sufficientMomentOrder_bound gap p hgap
  have hqpos : 1 ≤ q := by
    by_contra hnot
    have hzero : q = 0 := by omega
    change ((p + 1 : ℕ) : ℝ) ≤ (q : ℝ) * gap / 2 at hqbound
    rw [hzero] at hqbound
    have hp : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    norm_num at hqbound
    linarith
  have hbudget := eventually_pattern_switching_budget d (2 * (q : ℝ) * ρ)
    ((q : ℝ) * (2 * (J : ℝ) + 1)) (by omega) (by positivity) (by positivity)
  have hthreshold := eventually_const_mul_log_rpow_le ((q : ℝ) * C) ((3 : ℕ) : ℝ) gap hgap
  have htail := eventually_chosen_moment_decay C gap 3 p hC hgap
  filter_upwards [hbudget, hthreshold, htail, eventually_log_ge_nat 1,
    Filter.eventually_ge_atTop 1] with N hbudget hthreshold htail hlog hN
  let R := logarithmicRadius (c / 4) d N + J
  let K := q * (2 * R + 1)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNgap : 0 < (N : ℝ) ^ gap := Real.rpow_pos_of_pos hn _
  have hNc : 0 < (N : ℝ) ^ (3 * c / 4) := Real.rpow_pos_of_pos hn _
  have hNgamma : 0 < (N : ℝ) ^ γ := Real.rpow_pos_of_pos hn _
  have hnum := universal_badCenter_numerator_bound d N J c hd hc hN hlog
  change (universalBadCenterNumerator d R : ℝ) ≤ C * Real.log (N : ℝ) ^ 3 * (N : ℝ) ^ (3 * c / 4) at hnum
  have hr := structuralRadius_le_log d N c hd hc hN
  change (logarithmicRadius (c / 4) d N : ℝ) ≤ ρ * Real.log (N : ℝ) at hr
  have hK : (K : ℝ) ≤ (2 * (q : ℝ) * ρ) * Real.log (N : ℝ) + (q : ℝ) * (2 * (J : ℝ) + 1) := by
    have hh := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    dsimp only [K, R]
    push_cast
    nlinarith
  have hcombine : (N : ℝ) ^ gap * (N : ℝ) ^ (3 * c / 4) = (N : ℝ) ^ γ := by
    rw [← Real.rpow_add hn]
    congr 1
    dsimp [gap]
    ring
  have hthreshold' : ((q : ℝ) * C) * Real.log (N : ℝ) ^ 3 ≤ (N : ℝ) ^ gap := by
    simpa only [Real.rpow_natCast] using hthreshold
  have hcount : ((q * universalBadCenterNumerator d R : ℕ) : ℝ) ≤ (N : ℝ) ^ γ := by
    calc
      _ = (q : ℝ) * (universalBadCenterNumerator d R : ℝ) := by rw [Nat.cast_mul]
      _ ≤ (q : ℝ) * (C * Real.log (N : ℝ) ^ 3 * (N : ℝ) ^ (3 * c / 4)) :=
        mul_le_mul_of_nonneg_left hnum (Nat.cast_nonneg _)
      _ = ((q : ℝ) * C * Real.log (N : ℝ) ^ 3) * (N : ℝ) ^ (3 * c / 4) := by ring
      _ ≤ (N : ℝ) ^ gap * (N : ℝ) ^ (3 * c / 4) := mul_le_mul_of_nonneg_right hthreshold' hNc.le
      _ = _ := hcombine
  have hratio : (universalBadCenterNumerator d R : ℝ) / (N : ℝ) ^ γ ≤
      C * Real.log (N : ℝ) ^ 3 / (N : ℝ) ^ gap := by
    calc
      _ ≤ (C * Real.log (N : ℝ) ^ 3 * (N : ℝ) ^ (3 * c / 4)) / (N : ℝ) ^ γ :=
        div_le_div_of_nonneg_right hnum hNgamma.le
      _ = _ := by rw [← hcombine]; field_simp [ne_of_gt hNgap, ne_of_gt hNc]; ring
  refine ⟨by omega, hqpos, hbudget K hK, hcount, ?_⟩
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ (universalBadCenterNumerator d R : ℝ) / (N : ℝ) ^ γ by positivity) hratio q
  exact (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)).trans htail

/-- Every fixed-radius-offset count has an arbitrary polynomial tail in the
actual uniform ensemble, without any structural-event restriction. -/
theorem eventually_universal_badCenter_probability (d J p : ℕ) (c γ : ℝ)
    (hd : 3 ≤ d) (hc : 0 ≤ c) (hγ : 3 * c / 4 < γ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        (N : ℝ) ^ γ < ((nonTreeCenters g.graph (logarithmicRadius (c / 4) d N + J)).card : ℝ)) ≤
        1 / (N : ℝ) ^ p := by
  filter_upwards [eventually_universal_badCenter_budgets d J p c γ hd hc hγ] with N hnum
  dsimp only at hnum
  obtain ⟨hN, hq, hbudget, hthreshold, htail⟩ := hnum
  exact (RegularGraph.universal_badCenters_tail_bound _ _ _ hd hq le_rfl hN hbudget
    ((N : ℝ) ^ γ) (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) γ) hthreshold).trans htail

end LocalLaw
