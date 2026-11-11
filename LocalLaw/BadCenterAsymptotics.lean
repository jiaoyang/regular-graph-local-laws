import LocalLaw.BadCenterCycleCounting
import LocalLaw.ParameterGrowth

/-!
# Bad-center counts at the actual logarithmic structural radius

The switching denominator budget, radius rounding, and first-moment estimate
are combined. For every gamma>3c/4 the probability of more than N^gamma bad
radius-R centers tends to zero, with R=floor((c/4)log N/log(d-1)). No expected
count or finite-size slack bound is supplied as a hypothesis.
-/

namespace LocalLaw

noncomputable def structuralRadiusCoefficient (d : ℕ) (c : ℝ) : ℝ :=
  (c / 4) / Real.log ((d - 1 : ℕ) : ℝ)

noncomputable def badCenterMomentConstant (d : ℕ) (c : ℝ) : ℝ :=
  2 * ((d : ℝ) + 1) * (2 * structuralRadiusCoefficient d c + 2) ^ 2 * ((d - 1 : ℕ) : ℝ)

/-- The precise integer radius is bounded by its real logarithmic coordinate. -/
theorem structuralRadius_le_log (d N : ℕ) (c : ℝ) (hd : 3 ≤ d)
    (hc : 0 ≤ c) (hN : 1 ≤ N) :
    (logarithmicRadius (c / 4) d N : ℝ) ≤ structuralRadiusCoefficient d c * Real.log (N : ℝ) := by
  have hk : (1 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < d - 1 by omega)
  have hlogk := Real.log_pos hk
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hcoord : 0 ≤ (c / 4) * Real.log (N : ℝ) / Real.log ((d - 1 : ℕ) : ℝ) := by positivity
  have hf := Nat.floor_le hcoord
  change (logarithmicRadius (c / 4) d N : ℝ) ≤ _ at hf
  convert hf using 1
  unfold structuralRadiusCoefficient
  ring

/-- The actual first-moment numerator has rate log(N)^2*N^(3c/4). -/
theorem badCenter_numerator_bound (d N : ℕ) (c : ℝ) (hd : 3 ≤ d)
    (hc : 0 ≤ c) (hN : 1 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ)) :
    let R := logarithmicRadius (c / 4) d N
    ((2 * (d + 1) * (2 * R + 2) ^ 2 * (d - 1) ^ (3 * R + 1) : ℕ) : ℝ) ≤
      badCenterMomentConstant d c * Real.log (N : ℝ) ^ 2 * (N : ℝ) ^ (3 * c / 4) := by
  let R := logarithmicRadius (c / 4) d N
  let ρ := structuralRadiusCoefficient d c
  let k : ℝ := ((d - 1 : ℕ) : ℝ)
  have hk : 1 < k := by dsimp [k]; exact_mod_cast (show 1 < d - 1 by omega)
  have hkp : 0 < k := by linarith
  have hnp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hρ : 0 ≤ ρ := div_nonneg (by positivity) (Real.log_pos hk).le
  have hr := structuralRadius_le_log d N c hd hc hN
  change (R : ℝ) ≤ ρ * Real.log (N : ℝ) at hr
  have hlinear : 2 * (R : ℝ) + 2 ≤ (2 * ρ + 2) * Real.log (N : ℝ) := by nlinarith
  have hsquare := pow_le_pow_left₀ (show 0 ≤ 2 * (R : ℝ) + 2 by positivity) hlinear 2
  have hp := logarithmicRadius_power_bound (c / 4) d N (by positivity) hd hN
  have hpr : k ^ R ≤ (N : ℝ) ^ (c / 4) := hp
  have hcube := pow_le_pow_left₀ (pow_nonneg hkp.le R) hpr 3
  have hNp : ((N : ℝ) ^ (c / 4)) ^ (3 : ℕ) = (N : ℝ) ^ (3 * c / 4) := by
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hnp.le]
    congr 1
    norm_num
    ring
  rw [hNp] at hcube
  have hpower : k ^ (3 * R + 1) ≤ k * (N : ℝ) ^ (3 * c / 4) := by
    calc
      k ^ (3 * R + 1) = k * (k ^ R) ^ 3 := by
        rw [pow_add, pow_one, show 3 * R = R * 3 by omega, pow_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcube hkp.le
  change ((2 * (d + 1) * (2 * R + 2) ^ 2 * (d - 1) ^ (3 * R + 1) : ℕ) : ℝ) ≤ _
  push_cast
  have hprod := mul_le_mul hsquare hpower (pow_nonneg hkp.le _) (sq_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ 2 * ((d : ℝ) + 1) by positivity)
  convert hscaled using 1 <;> dsimp [badCenterMomentConstant, ρ, k] <;> ring

/-- The bad-center portion of the source structural event has probability
arbitrarily close to one, proved under the actual uniform regular-graph law. -/
theorem eventually_badCenter_tail_small (d : ℕ) (c γ δ : ℝ) (hd : 3 ≤ d)
    (hc : 0 ≤ c) (hγ : 3 * c / 4 < γ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        (N : ℝ) ^ γ < ((nonTreeCenters g.graph (logarithmicRadius (c / 4) d N)).card : ℝ)) ≤ δ := by
  let ρ := structuralRadiusCoefficient d c
  let C := badCenterMomentConstant d c
  have hk : (1 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < d - 1 by omega)
  have hρ : 0 ≤ ρ := div_nonneg (by positivity) (Real.log_pos hk).le
  have hbudget := eventually_pattern_switching_budget d (2 * ρ) 1 (by omega) (by positivity) (by norm_num)
  have hsmall := eventually_const_mul_log_rpow_le (C / δ) 2 (γ - 3 * c / 4) (by linarith)
  filter_upwards [hbudget, hsmall, eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1]
    with N hbudget hsmall hlog hN
  let R := logarithmicRadius (c / 4) d N
  let K := 2 * R + 1
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr := structuralRadius_le_log d N c hd hc hN
  have hK : (K : ℝ) ≤ 2 * ρ * Real.log (N : ℝ) + 1 := by
    dsimp [K]
    push_cast
    change (R : ℝ) ≤ ρ * Real.log (N : ℝ) at hr
    linarith
  have htail := RegularGraph.badCenters_strict_tail_bound R K hd le_rfl (by omega)
    (hbudget K hK) ((N : ℝ) ^ γ) (Real.rpow_pos_of_pos hn γ)
  have hnum := badCenter_numerator_bound d N c hd hc hN hlog
  have hsmall' : C * Real.log (N : ℝ) ^ 2 ≤ δ * (N : ℝ) ^ (γ - 3 * c / 4) := by
    have hh : (C / δ) * Real.log (N : ℝ) ^ 2 ≤ (N : ℝ) ^ (γ - 3 * c / 4) := by
      simpa only [Real.rpow_two] using hsmall
    have hm := mul_le_mul_of_nonneg_left hh hδ.le
    calc
      C * Real.log (N : ℝ) ^ 2 = δ * ((C / δ) * Real.log (N : ℝ) ^ 2) := by
        field_simp [ne_of_gt hδ]
      _ ≤ _ := hm
  have hcombine : (N : ℝ) ^ (γ - 3 * c / 4) * (N : ℝ) ^ (3 * c / 4) = (N : ℝ) ^ γ := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  apply htail.trans
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hn γ)).mpr
  calc
    _ ≤ C * Real.log (N : ℝ) ^ 2 * (N : ℝ) ^ (3 * c / 4) := hnum
    _ ≤ (δ * (N : ℝ) ^ (γ - 3 * c / 4)) * (N : ℝ) ^ (3 * c / 4) :=
      mul_le_mul_of_nonneg_right hsmall' (Real.rpow_nonneg hn.le _)
    _ = δ * (N : ℝ) ^ γ := by rw [mul_assoc, hcombine]


/-- Complementary events partition a nonempty finite uniform ensemble. -/
theorem finiteUniform_eventMass_complement_sum {X : Type*} [Fintype X] [Nonempty X]
    (P : X → Prop) :
    eventMass (finiteUniformWeight X) P + eventMass (finiteUniformWeight X) (fun x => ¬ P x) = 1 := by
  classical
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ x : X, finiteUniformWeight X x := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : P x <;> simp [hx]
    _ = 1 := finiteUniformWeight_total

/-- The actual bad-center good event has large uniform mass on every nonempty
regular-graph ensemble, with the full large-N choice proved above. -/
theorem eventually_badCenter_good_mass (d : ℕ) (c γ δ : ℝ) (hd : 3 ≤ d)
    (hc : 0 ≤ c) (hγ : 3 * c / 4 < γ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in Filter.atTop, Nonempty (RegularGraph N d) →
      1 - δ ≤ eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        ((nonTreeCenters g.graph (logarithmicRadius (c / 4) d N)).card : ℝ) ≤ (N : ℝ) ^ γ) := by
  filter_upwards [eventually_badCenter_tail_small d c γ δ hd hc hγ hδ] with N htail
  intro hnonempty
  letI : Nonempty (RegularGraph N d) := hnonempty
  let P : RegularGraph N d → Prop := fun g =>
    ((nonTreeCenters g.graph (logarithmicRadius (c / 4) d N)).card : ℝ) ≤ (N : ℝ) ^ γ
  have hcompl : eventMass RegularGraph.weight (fun g => ¬ P g) ≤ δ := by
    simpa only [P, not_le] using htail
  have hsum := finiteUniform_eventMass_complement_sum P
  change eventMass RegularGraph.weight P + eventMass RegularGraph.weight (fun g => ¬ P g) = 1 at hsum
  linarith

end LocalLaw
