import LocalLaw.SourceObservationMean
import LocalLaw.ActualWeightedConcentration

/-!
# Actual source one-edge weighted concentration

The masked singleton observation has its proved bound and true one-edge bias.
The actual independent uniform sampling fiber therefore controls every finite
weight family simultaneously, with a derived inverse-power probability.
-/

open Filter
open scoped BigOperators NNReal
noncomputable section
namespace LocalLaw
local instance sourceObservationConcentrationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem graphPaperError_positive_of_log (a d N r : ℕ) (z : ℂ) (hd : 3 ≤ d)
    (hlog : 1 ≤ Real.log (N : ℝ)) (hz : 0 ≤ z.im) : 0 < graphPaperError a d N r z := by
  have hL : 0 < Real.log (N : ℝ) := by linarith
  have hk : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
  have hf : 0 < localizationErrorFloor a d N r := by unfold localizationErrorFloor; positivity
  exact hf.trans_le (graphPaperError_lower a d N r z hlog hz)

namespace RegularGraph

/-- Source (6.2) with arbitrary deterministic finite weights. Observation
boundedness, true bias, independence and the inverse-power tail are all
conclusions of actual source assumptions. -/
theorem eventually_sourceSingletonObservation_concentration (a b d q : ℕ) (c β γ B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hγ : c / 4 < γ) (hgap : γ + β < 1)
    (hB : 0 ≤ B) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∀ Cq badCount : ℕ, badCount ≤ ⌊(N : ℝ) ^ γ⌋₊ →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ (J : Type) [Fintype J], Fintype.card J ≤ N →
      ∀ w : J → BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)) → ℂ,
      eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
        (fun samples => ∃ j : J,
          Real.log (N : ℝ) * (DeficientGraph.singletonObservationConstant d * C1 *
              g.sourcePrime a (logarithmicRadius β d N) z) * Real.sqrt (∑ α, ‖w j α‖ ^ 2) +
            (3 * graphPaperError a d N (logarithmicRadius β d N) z / Real.log (N : ℝ) ^ 16) *
              (∑ α, ‖w j α‖) <
          ‖∑ α, w j α * (g.sourceSingletonObservation
              (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))
              (effectiveModelRadius a d N β) (logarithmicRadius (c / 4) d N / 4) z (g.Q z) (samples α) -
                (g.Q z - cavityIterate z (g.Q z) (effectiveModelRadius a d N β + 1)))‖) ≤
        1 / (N : ℝ) ^ q := by
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_sourceSingletonObservation_bound a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceSingletonObservation_mean_bias a b d c β γ B C1 ha hb hd hc hβ hβc hγ hgap hB hC1,
    eventually_gaussian_log_tail_le_inverse_power (q + 1), eventually_resampling_ball_budget a d hd,
    hdepth, eventually_log_ge_nat 1, eventually_ge_atTop 2]
    with N hZ hmean htail hball hdepth hlog hN
  intro g o z hz hzB hscale Cq badCount hbad hplus J _ hJ w
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let ell := actualCavityDepth a d N z - 1
  let r := effectiveModelRadius a d N β
  let R := logarithmicRadius (c / 4) d N
  let T := graphBallVertices g.graph o ell
  let Z := g.sourceSingletonObservation T r (R / 4) z (g.Q z)
  let target := g.Q z - cavityIterate z (g.Q z) (r + 1)
  let amplitude := DeficientGraph.singletonObservationConstant d * C1 * g.sourcePrime a (logarithmicRadius β d N) z
  have hLp : 0 < L := by linarith
  have hεp : 0 < ε := graphPaperError_positive_of_log a d N _ z hd hlog hz.le
  have hprime : 0 < g.sourcePrime a (logarithmicRadius β d N) z := by
    change 0 < L ^ 3 * ε
    positivity
  have hamp : 0 < amplitude := by
    have hC1p : 0 < C1 := by linarith
    have hconst : 0 < DeficientGraph.singletonObservationConstant d := by
      unfold DeficientGraph.singletonObservationConstant
      positivity
    exact mul_pos (mul_pos hconst hC1p) hprime
  let bound : ℝ≥0 := ⟨amplitude, hamp.le⟩
  have hboundpos : 0 < bound := hamp
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hT : 4 * Nat.card T ≤ N := by
    apply (Nat.mul_le_mul_left 4 ((g.ball_card_bound o ell).trans
      (Nat.pow_le_pow_right (by omega : 0 < d + 1) hell))).trans hball
  have hout := g.outside_edge_nonempty T (by omega) (by omega) hT
  have hbound : ∀ e, ‖Z e‖ ≤ (bound : ℝ) :=
    fun e => hZ g o z hz hscale hzB Cq badCount hplus e
  have hbias : ‖finiteComplexMean Z - target‖ ≤ 3 * ε / L ^ 16 :=
    hmean g o z hz hzB hscale Cq badCount hbad hplus
  have hfamily := localSampling_weighted_family_concentration g.graph T hout (fun _ e => Z e)
    (fun _ => target) w Finset.univ bound hboundpos (fun _ _ e => hbound e)
    (3 * ε / L ^ 16) (fun _ _ => hbias) L hLp.le
  apply hfamily.trans
  have hJreal : (Fintype.card J : ℝ) ≤ N := Nat.cast_le.mpr hJ
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  calc
    _ ≤ (N : ℝ) * (1 / (N : ℝ) ^ (q + 1)) :=
      mul_le_mul hJreal htail (by positivity) (by positivity)
    _ = 1 / (N : ℝ) ^ q := by rw [pow_succ]; field_simp; ring

end RegularGraph
end LocalLaw
