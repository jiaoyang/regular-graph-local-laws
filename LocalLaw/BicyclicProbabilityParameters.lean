import LocalLaw.BadCenterAsymptotics

/-!
# Numerical probability budget for four-path bicyclic witnesses

Four tail lengths and three graft labels give a polynomial-in-R family size.
At R=floor((c/4)log N/log(d-1)), its sharp (d-1)^(4R+1)/N expectation vanishes
for every c<1. The actual switching denominator budget is realized too.
The canonical encoding and finite family probability bound are separate inputs
to the final graph-probability theorem.
-/

namespace LocalLaw

noncomputable def bicyclicFamilyConstant (d : ℕ) (c : ℝ) : ℝ :=
  2 * (((d ^ d : ℕ) : ℝ) ^ 8) * ((d - 1 : ℕ) : ℝ) *
    (structuralRadiusCoefficient d c + 1) ^ 4 * (4 * structuralRadiusCoefficient d c + 2) ^ 3

/-- The literal four-path parameter count times the expected-copy numerator
has a seventh logarithmic power and the sharp N^c rate. -/
theorem bicyclic_family_numerator_bound (d N : ℕ) (c : ℝ) (hd : 3 ≤ d)
    (hc : 0 ≤ c) (hN : 1 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ)) :
    let R := logarithmicRadius (c / 4) d N
    (((R + 1) ^ 4 * (4 * R + 2) ^ 3 : ℕ) : ℝ) *
      (2 * (((d ^ d : ℕ) : ℝ) ^ 8) * (((d - 1 : ℕ) : ℝ) ^ (4 * R + 1))) ≤
        bicyclicFamilyConstant d c * Real.log (N : ℝ) ^ 7 * (N : ℝ) ^ c := by
  let R := logarithmicRadius (c / 4) d N
  let ρ := structuralRadiusCoefficient d c
  let k : ℝ := ((d - 1 : ℕ) : ℝ)
  have hk : 1 < k := by dsimp [k]; exact_mod_cast (show 1 < d - 1 by omega)
  have hkp : 0 < k := by linarith
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hρ : 0 ≤ ρ := div_nonneg (by positivity) (Real.log_pos hk).le
  have hr := structuralRadius_le_log d N c hd hc hN
  change (R : ℝ) ≤ ρ * Real.log (N : ℝ) at hr
  have hfirst : (R : ℝ) + 1 ≤ (ρ + 1) * Real.log (N : ℝ) := by nlinarith
  have hrest : 4 * (R : ℝ) + 2 ≤ (4 * ρ + 2) * Real.log (N : ℝ) := by nlinarith
  have h₄ := pow_le_pow_left₀ (by positivity : 0 ≤ (R : ℝ) + 1) hfirst 4
  have h₃ := pow_le_pow_left₀ (by positivity : 0 ≤ 4 * (R : ℝ) + 2) hrest 3
  have hp := logarithmicRadius_power_bound (c / 4) d N (by positivity) hd hN
  have hp' : k ^ R ≤ (N : ℝ) ^ (c / 4) := hp
  have hfour := pow_le_pow_left₀ (pow_nonneg hkp.le R) hp' 4
  have hNpower : ((N : ℝ) ^ (c / 4)) ^ (4 : ℕ) = (N : ℝ) ^ c := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hn.le]
    congr 1
    norm_num
  rw [hNpower] at hfour
  have hpower : k ^ (4 * R + 1) ≤ k * (N : ℝ) ^ c := by
    calc
      _ = k * (k ^ R) ^ 4 := by
        rw [pow_add, pow_one, show 4 * R = R * 4 by omega, pow_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfour hkp.le
  have hfactor := mul_le_mul h₄ h₃ (by positivity) (by positivity)
  have hweighted := mul_le_mul_of_nonneg_left hpower
    (show 0 ≤ 2 * (((d ^ d : ℕ) : ℝ) ^ 8) by positivity)
  have hfinal := mul_le_mul hfactor hweighted (by positivity) (by positivity)
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hfinal ⊢
  convert hfinal using 1
  all_goals
    dsimp only [bicyclicFamilyConstant, ρ, k, R]
    simp only [Nat.cast_pow]
    ring

/-- All finite-N numeric assumptions for the expected bicyclic-family union
bound hold eventually, and its probability budget is arbitrarily small. -/
theorem eventually_bicyclic_family_budget (d : ℕ) (c δ : ℝ) (hd : 3 ≤ d)
    (hc : 0 ≤ c) (hc₁ : c < 1) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      let R := logarithmicRadius (c / 4) d N
      let K := 4 * R + 2
      0 < N ∧ 2 * K * RegularGraph.patternSwitchSlack d K ≤ N * d ∧
        (((R + 1) ^ 4 * (4 * R + 2) ^ 3 : ℕ) : ℝ) *
          (2 * (((d ^ d : ℕ) : ℝ) ^ 8) * (((d - 1 : ℕ) : ℝ) ^ (4 * R + 1)) / (N : ℝ)) ≤ δ := by
  let ρ := structuralRadiusCoefficient d c
  let C := bicyclicFamilyConstant d c
  have hk : (1 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < d - 1 by omega)
  have hρ : 0 ≤ ρ := div_nonneg (by positivity) (Real.log_pos hk).le
  have hbudget := eventually_pattern_switching_budget d (4 * ρ) 2 (by omega) (by positivity) (by norm_num)
  have hsmall := eventually_const_mul_log_rpow_le (C / δ) ((7 : ℕ) : ℝ) (1 - c) (by linarith)
  filter_upwards [hbudget, hsmall, eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1]
    with N hbudget hsmall hlog hN
  let R := logarithmicRadius (c / 4) d N
  let K := 4 * R + 2
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr := structuralRadius_le_log d N c hd hc hN
  change (R : ℝ) ≤ ρ * Real.log (N : ℝ) at hr
  have hK : (K : ℝ) ≤ 4 * ρ * Real.log (N : ℝ) + 2 := by dsimp [K]; push_cast; linarith
  have hnum := bicyclic_family_numerator_bound d N c hd hc hN hlog
  have hsmall' : C * Real.log (N : ℝ) ^ 7 ≤ δ * (N : ℝ) ^ (1 - c) := by
    have hh : (C / δ) * Real.log (N : ℝ) ^ 7 ≤ (N : ℝ) ^ (1 - c) := by
      simpa only [Real.rpow_natCast] using hsmall
    calc
      _ = δ * ((C / δ) * Real.log (N : ℝ) ^ 7) := by field_simp [ne_of_gt hδ]
      _ ≤ _ := mul_le_mul_of_nonneg_left hh hδ.le
  have hcombine : (N : ℝ) ^ (1 - c) * (N : ℝ) ^ c = (N : ℝ) := by
    rw [← Real.rpow_add hn, show 1 - c + c = 1 by ring, Real.rpow_one]
  refine ⟨by omega, hbudget K hK, ?_⟩
  have heq : (((R + 1) ^ 4 * (4 * R + 2) ^ 3 : ℕ) : ℝ) *
      (2 * (((d ^ d : ℕ) : ℝ) ^ 8) * (((d - 1 : ℕ) : ℝ) ^ (4 * R + 1)) / (N : ℝ)) =
        ((((R + 1) ^ 4 * (4 * R + 2) ^ 3 : ℕ) : ℝ) *
          (2 * (((d ^ d : ℕ) : ℝ) ^ 8) * (((d - 1 : ℕ) : ℝ) ^ (4 * R + 1)))) / (N : ℝ) := by ring
  rw [heq]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ C * Real.log (N : ℝ) ^ 7 * (N : ℝ) ^ c := hnum
    _ ≤ (δ * (N : ℝ) ^ (1 - c)) * (N : ℝ) ^ c :=
      mul_le_mul_of_nonneg_right hsmall' (Real.rpow_nonneg hn.le _)
    _ = δ * (N : ℝ) := by rw [mul_assoc, hcombine]

end LocalLaw
