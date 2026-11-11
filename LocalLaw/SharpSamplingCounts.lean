import LocalLaw.SharpBallCounting
import LocalLaw.ClosureParameters

/-!
# Actual boundary-label counts at the selected source radius

The sharp d-1 ball growth and integer radius bounds yield the source
polylogarithmic count mu <= d(d+1)(log N)^(2a), uniformly in the center, graph,
and spectral-parameter-dependent nonresonant depth choice.
-/

namespace LocalLaw

/-- The larger integer log-log radius has the intended exponential base. -/
theorem doubleLogRadius_base_power_bound (a d N : ℕ) (hd : 3 ≤ d)
    (hL : 1 ≤ Real.log (N : ℝ)) :
    (((d - 1 : ℕ) : ℝ) ^ doubleLogRadius a d N) ≤ Real.log (N : ℝ) ^ (2 * a) := by
  let k : ℝ := ((d - 1 : ℕ) : ℝ)
  let L := Real.log (N : ℝ)
  have hk : 1 < k := by dsimp [k]; exact_mod_cast (show 1 < d - 1 by omega)
  have hkp : 0 < k := by linarith
  have hlogk : 0 < Real.log k := Real.log_pos hk
  have hLp : 0 < L := by dsimp [L]; linarith
  have hcoord : 0 ≤ ((2 * a : ℕ) : ℝ) * Real.log L / Real.log k := by
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hL)
    · exact hlogk.le
  have hf := Nat.floor_le hcoord
  change (doubleLogRadius a d N : ℝ) ≤ _ at hf
  have hp := Real.rpow_le_rpow_of_exponent_le hk.le hf
  have hid : k ^ (((2 * a : ℕ) : ℝ) * Real.log L / Real.log k) = L ^ (2 * a : ℕ) := by
    rw [Real.rpow_def_of_pos hkp, ← Real.rpow_natCast L (2 * a), Real.rpow_def_of_pos hLp]
    congr 1
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hlogk)]
    ring
  simpa only [hid, Real.rpow_natCast] using hp

namespace RegularGraph
variable {N d : ℕ}

/-- Actual boundary labels at every radius below the source upper cutoff. -/
theorem boundary_card_log_bound (g : RegularGraph N d) (o : Fin N) (a ell : ℕ)
    (hd : 3 ≤ d) (hL : 1 ≤ Real.log (N : ℝ)) (hell : ell ≤ doubleLogRadius a d N) :
    (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) ≤
      (d : ℝ) * ((d : ℝ) + 1) * Real.log (N : ℝ) ^ (2 * a) := by
  have hnat := g.boundary_card_sharp o ell hd
  have hcast : (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) ≤
      (d : ℝ) * ((d : ℝ) + 1) * (((d - 1 : ℕ) : ℝ) ^ ell) := by exact_mod_cast hnat
  have hk : (1 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ d - 1 by omega)
  have hpower : (((d - 1 : ℕ) : ℝ) ^ ell) ≤ Real.log (N : ℝ) ^ (2 * a) :=
    (pow_le_pow_right₀ hk hell).trans (doubleLogRadius_base_power_bound a d N hd hL)
  exact hcast.trans (mul_le_mul_of_nonneg_left hpower (by positivity))

end RegularGraph

/-- The count bound is realized for the actual chosen radius, with no
spectral-parameter restrictions or remaining radius comparison premise. -/
theorem eventually_actual_boundary_card_log_bound (a d : ℕ) (hd : 3 ≤ d) (ha : 0 < a) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ g : RegularGraph N d, ∀ o : Fin N, ∀ z : ℂ,
      (Nat.card (BoundaryOrientedEdge g.graph
        (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))) : ℝ) ≤
        (d : ℝ) * ((d : ℝ) + 1) * Real.log (N : ℝ) ^ (2 * a) := by
  have hr := (lowerLogLogRadius_tendsto a d ha hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [hr, eventually_log_ge_nat 1] with N hr hL
  intro g o z
  exact g.boundary_card_log_bound o a _ hd hL (actualCavityDepth_radius_bounds a d N z hr).2

end LocalLaw
