import LocalLaw.ResamplingRadiusGrowth
import LocalLaw.GraphBallCounting

/-!
# Realization of the local sampling hypotheses for the integer log-log radius

The small-neighborhood cardinality, nonempty sampling fibers, and the actual
endpoint probability bound hold uniformly in every regular graph and center
for all sufficiently large N. They are conclusions, not parameter hypotheses.
-/

open Filter

namespace LocalLaw

theorem eventually_actual_resampling_ball_small (a d : ℕ) (hd : 3 ≤ d) :
    ∀ᶠ N : ℕ in atTop, ∀ g : RegularGraph N d, ∀ o : Fin N,
      4 * Nat.card (graphBallVertices g.graph o (doubleLogRadius a d N)) ≤ N := by
  filter_upwards [eventually_resampling_ball_budget a d hd] with N hN
  intro g o
  exact g.ball_small o _ hN

theorem eventually_actual_local_sampling_nonempty (a d : ℕ) (hd : 3 ≤ d) :
    ∀ᶠ N : ℕ in atTop, ∀ g : RegularGraph N d, ∀ o : Fin N,
      Nonempty (LocalSamplingFiber g.graph (graphBallVertices g.graph o (doubleLogRadius a d N))) := by
  filter_upwards [eventually_resampling_ball_budget a d hd, eventually_ge_atTop 1] with N hN hpositive
  intro g o
  exact g.ball_sampling_fiber_nonempty o _ (by omega) (by omega) hN

/-- Source Proposition5.9 for the actual N-dependent resampling radius. -/
theorem eventually_actual_endpoint_probability (a d : ℕ) (hd : 3 ≤ d) :
    ∀ᶠ N : ℕ in atTop, ∀ g : RegularGraph N d, ∀ o v : Fin N,
      eventMass (finiteUniformWeight (OutsideOrientedEdge g.graph
        (graphBallVertices g.graph o (doubleLogRadius a d N))))
        (fun e => outsideEdgeFirst g.graph (graphBallVertices g.graph o (doubleLogRadius a d N)) e = v)
        ≤ 2 / (N : ℝ) ∧
      eventMass (finiteUniformWeight (OutsideOrientedEdge g.graph
        (graphBallVertices g.graph o (doubleLogRadius a d N))))
        (fun e => outsideEdgeSecond g.graph (graphBallVertices g.graph o (doubleLogRadius a d N)) e = v)
        ≤ 2 / (N : ℝ) := by
  filter_upwards [eventually_resampling_ball_budget a d hd, eventually_ge_atTop 1] with N hN hpositive
  intro g o v
  exact g.ball_endpoint_probability o _ (by omega) (by omega) hN v

end LocalLaw
