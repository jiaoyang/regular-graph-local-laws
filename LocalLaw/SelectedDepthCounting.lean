import LocalLaw.SharpSamplingCounts

/-! # Logarithmic slack from the actual selected depth

The selected radius is about 3a/2 times log log N. Retaining this upper
bound, rather than the allowed 2a cutoff, leaves four logarithmic powers
for full switching benchmarks at the endpoint a = 12.
-/

namespace LocalLaw

/-- The adjacent-depth choice costs at most two above its real baseline. -/
theorem actualCavityDepth_strong_upper (a d N : ℕ) (z : ℂ)
    (hlo : 0 ≤ lowerLogLogRadius a d N) :
    ((actualCavityDepth a d N z - 1 : ℕ) : ℝ) ≤
      (3 / 2 : ℝ) * lowerLogLogRadius a d N + 2 := by
  have h := nonresonantDepth_bounds (semicircleRoot z) (baselineCavityDepth a d N)
  change baselineCavityDepth a d N ≤ actualCavityDepth a d N z ∧
    actualCavityDepth a d N z ≤ baselineCavityDepth a d N + 1 at h
  have hp : 1 ≤ actualCavityDepth a d N z := by
    dsimp [baselineCavityDepth] at h
    omega
  have hcast : (actualCavityDepth a d N z : ℝ) ≤
      (⌊(3 / 2 : ℝ) * lowerLogLogRadius a d N⌋₊ : ℝ) + 3 := by
    exact_mod_cast h.2
  rw [Nat.cast_sub hp, Nat.cast_one]
  have hf := Nat.floor_le (show 0 ≤ (3 / 2 : ℝ) * lowerLogLogRadius a d N by linarith)
  linarith

theorem selectedDepth_base_power_bound (a d N : ℕ) (z : ℂ)
    (ha : 12 ≤ a) (hd : 3 ≤ d) (hL : 1 ≤ Real.log (N : ℝ))
    (hdepth : 12 ≤ lowerLogLogRadius a d N) :
    (((d - 1 : ℕ) : ℝ) ^ (actualCavityDepth a d N z - 1)) ≤
      Real.log (N : ℝ) ^ (2 * a - 4) := by
  let k : ℝ := ((d - 1 : ℕ) : ℝ)
  let L := Real.log (N : ℝ)
  have hk : 1 < k := by dsimp [k]; exact_mod_cast (show 1 < d - 1 by omega)
  have hkp : 0 < k := by linarith
  have hlogk : 0 < Real.log k := Real.log_pos hk
  have hLp : 0 < L := by dsimp [L]; linarith
  have hratio : 0 ≤ Real.log L / Real.log k :=
    div_nonneg (Real.log_nonneg hL) hlogk.le
  have haR : (12 : ℝ) ≤ a := by exact_mod_cast ha
  have hsub : ((2 * a - 4 : ℕ) : ℝ) = 2 * (a : ℝ) - 4 := by
    rw [Nat.cast_sub (by omega : 4 ≤ 2 * a)]
    push_cast
    ring
  have hu := actualCavityDepth_strong_upper a d N z (by linarith)
  have hu' : ((actualCavityDepth a d N z - 1 : ℕ) : ℝ) ≤
      (5 / 3 : ℝ) * lowerLogLogRadius a d N := by linarith
  have he : ((actualCavityDepth a d N z - 1 : ℕ) : ℝ) ≤
      ((2 * a - 4 : ℕ) : ℝ) * Real.log L / Real.log k := by
    have hc : (5 / 3 : ℝ) * (a : ℝ) ≤ ((2 * a - 4 : ℕ) : ℝ) := by
      rw [hsub]
      linarith
    have hm := mul_le_mul_of_nonneg_right hc hratio
    calc
      _ ≤ (5 / 3 : ℝ) * lowerLogLogRadius a d N := hu'
      _ = ((5 / 3 : ℝ) * (a : ℝ)) * (Real.log L / Real.log k) := by
        dsimp only [lowerLogLogRadius, L, k]
        ring
      _ ≤ ((2 * a - 4 : ℕ) : ℝ) * (Real.log L / Real.log k) := hm
      _ = _ := by ring
  have hp := Real.rpow_le_rpow_of_exponent_le hk.le he
  have hid : k ^ (((2 * a - 4 : ℕ) : ℝ) * Real.log L / Real.log k) = L ^ (2 * a - 4) := by
    rw [Real.rpow_def_of_pos hkp, ← Real.rpow_natCast L (2 * a - 4), Real.rpow_def_of_pos hLp]
    congr 1
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hlogk)]
    ring
  simpa only [hid, Real.rpow_natCast] using hp

/-- Uniformly over the spectral-dependent depth and every regular graph. -/
theorem eventually_actual_selected_counts (a d : ℕ) (ha : 12 ≤ a) (hd : 3 ≤ d) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ g : RegularGraph N d, ∀ o : Fin N, ∀ z : ℂ,
      let ell := actualCavityDepth a d N z - 1
      (Nat.card (graphBallVertices g.graph o ell) : ℝ) ≤
        ((d : ℝ) + 1) * Real.log (N : ℝ) ^ (2 * a - 4) ∧
      (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) ≤
        (d : ℝ) * ((d : ℝ) + 1) * Real.log (N : ℝ) ^ (2 * a - 4) := by
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 12)
  filter_upwards [hdepth, eventually_log_ge_nat 1] with N hdepth hL
  intro g o z
  dsimp only
  have hp := selectedDepth_base_power_bound a d N z ha hd hL hdepth
  have hb : (Nat.card (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)) : ℝ) ≤
      ((d : ℝ) + 1) * (((d - 1 : ℕ) : ℝ) ^ (actualCavityDepth a d N z - 1)) := by
    exact_mod_cast g.ball_card_sharp o (actualCavityDepth a d N z - 1) hd
  have hc : (Nat.card (BoundaryOrientedEdge g.graph
      (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))) : ℝ) ≤
      (d : ℝ) * ((d : ℝ) + 1) * (((d - 1 : ℕ) : ℝ) ^ (actualCavityDepth a d N z - 1)) := by
    exact_mod_cast g.boundary_card_sharp o (actualCavityDepth a d N z - 1) hd
  exact ⟨hb.trans (mul_le_mul_of_nonneg_left hp (by positivity)),
    hc.trans (mul_le_mul_of_nonneg_left hp (by positivity))⟩

end LocalLaw
