import LocalLaw.SharpSamplingCounts

/-!
# The actual bad-center creation cost fits the auxiliary count

The selected boundary count is polylogarithmic and the source-radius ball
volume grows like N^(c/4). Every count exponent gamma>c/4 therefore absorbs
the literal deterministic switching cost, including its integer floor.
-/

noncomputable section
namespace LocalLaw
local instance resamplingStructuralCostDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_resampling_badCenter_cost (a d : ℕ) (c γ : ℝ)
    (hd : 3 ≤ d) (hc : 0 ≤ c) (hγ : c / 4 < γ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (ell : ℕ),
      ell ≤ doubleLogRadius a d N →
      4 * Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) *
        ((d + 1) * (d - 1) ^ logarithmicRadius (c / 4) d N) ≤ ⌊(N : ℝ) ^ γ⌋₊ := by
  let C : ℝ := 4 * (d : ℝ) * ((d : ℝ) + 1) ^ 2
  filter_upwards [eventually_const_mul_log_rpow_le C ((2 * a : ℕ) : ℝ) (γ - c / 4) (by linarith),
    eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1] with N hnum hlog hN
  intro g o ell hell
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  let μ : ℝ := Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
  let V : ℝ := (((d + 1) * (d - 1) ^ logarithmicRadius (c / 4) d N : ℕ) : ℝ)
  have hμ := g.boundary_card_log_bound o a ell hd hlog hell
  have hV : V ≤ ((d : ℝ) + 1) * (N : ℝ) ^ (c / 4) := by
    have hh := logarithmicRadius_power_bound (c / 4) d N (by linarith) hd hN
    dsimp only [V]
    push_cast
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  have hcost : 4 * μ * V ≤ (N : ℝ) ^ γ := by
    calc
      _ ≤ 4 * ((d : ℝ) * ((d : ℝ) + 1) * Real.log (N : ℝ) ^ (2 * a)) *
          (((d : ℝ) + 1) * (N : ℝ) ^ (c / 4)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hμ (by norm_num)
        · exact hV
        · dsimp only [V]; positivity
        · positivity
      _ = (C * Real.log (N : ℝ) ^ (2 * a)) * (N : ℝ) ^ (c / 4) := by dsimp only [C]; ring
      _ ≤ (N : ℝ) ^ (γ - c / 4) * (N : ℝ) ^ (c / 4) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [Real.rpow_natCast] using hnum
      _ = (N : ℝ) ^ γ := by rw [← Real.rpow_add hn]; congr 1; ring
  apply (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) γ)).mpr
  dsimp only [μ, V] at hcost
  exact_mod_cast hcost

end RegularGraph
end LocalLaw
