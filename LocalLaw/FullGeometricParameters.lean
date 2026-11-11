import LocalLaw.SourceFullGeometricEvent
import LocalLaw.GeometricSamplingParameters

/-!
# Arbitrary polynomial probability for the strengthened geometric event

The extra own-label collision term is absorbed using one more inverse power
of N in the already proved finite sampling budget. All source-radius and
auxiliary-count conditions are realized, including the chosen cavity depth.
-/

namespace LocalLaw
noncomputable section
local instance fullGeometricParameterDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
theorem eventually_sourceFullGeometricGood_probability (a d ω p : ℕ) (c γ : ℝ)
    (hd : 3 ≤ d) (hc : 0 < c) (hc₁ : c < 1) (hγ : γ < 1) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ᶠ N : ℕ in Filter.atTop,
      ∀ (g : RegularGraph N d) (o : Fin N) (ell : ℕ), ell ≤ doubleLogRadius a d N →
      graphBallExcess g.graph o (logarithmicRadius (c / 4) d N) ≤ ω →
      (nonTreeCenters g.graph (logarithmicRadius (c / 4) d N + 1)).card ≤ ⌊(N : ℝ) ^ γ⌋₊ →
      eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o ell))
        (fun S => ¬ SourceFullGeometricGood g.graph o ell (logarithmicRadius (c / 4) d N) ω
          (q - 1) (q - 1) (2 * q * (2 * (q - 1) + 1)) (q - 1) S) ≤
        4 / (N : ℝ) ^ p := by
  obtain ⟨q, hq, hnum⟩ := eventually_geometric_sampling_budget a d (p + 1) c γ hc₁ hγ
  refine ⟨q, hq, ?_⟩
  filter_upwards [hnum, eventually_resampling_ball_budget a d hd,
    eventually_resampling_radius_margin a d 2 2 (c / 4) hd (by linarith),
    eventually_log_ge_nat 1, Filter.eventually_ge_atTop 2] with N hnum hball hmargin hlog hN
  intro g o ell hell hexcess hbad
  let R := logarithmicRadius (c / 4) d N
  let μ : ℝ := Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
  let V : ℝ := (((d + 1) * (d - 1) ^ R : ℕ) : ℝ)
  let b : ℕ := ⌊(N : ℝ) ^ γ⌋₊
  have hT : 4 * Nat.card (graphBallVertices g.graph o ell) ≤ N := by
    apply (Nat.mul_le_mul_left 4 ((g.ball_card_bound o ell).trans
      (Nat.pow_le_pow_right (by omega : 0 < d + 1) hell))).trans hball
  have hmargin' : 2 * ell + 2 ≤ R := by dsimp only [R]; omega
  have hμ : μ ≤ (d : ℝ) * ((d : ℝ) + 1) * Real.log (N : ℝ) ^ (2 * a) :=
    g.boundary_card_log_bound o a ell hd hlog hell
  have hV : V ≤ ((d : ℝ) + 1) * (N : ℝ) ^ (c / 4) := by
    have hh := logarithmicRadius_power_bound (c / 4) d N (by linarith) hd (by omega)
    dsimp only [V, R]
    push_cast
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  have hb : (b : ℝ) ≤ (N : ℝ) ^ γ := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) γ)
  have hprob := g.localSampling_sourceFullGeometricGood_failure o ell R ω (q - 1) (q - 1) q (q - 1) b
    (by omega) hd hT hmargin' hexcess hbad
  have hexp : q - 1 + 1 = q := Nat.sub_add_cancel hq
  rw [hexp] at hprob
  have hbudget := hnum μ V (b : ℝ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hμ hV hb
  have hnonneg : 0 ≤ 2 * (N : ℝ) * (μ * (4 * V / N)) ^ q +
      (μ ^ 2 * (8 * V / N)) ^ q + (μ * (4 * (b : ℝ) / N)) ^ q := by positivity
  have hdouble : 2 * (N : ℝ) * (μ * (4 * V / N)) ^ q + 2 * (4 * μ ^ 2 * V / N) ^ q +
      (μ ^ 2 * (8 * V / N)) ^ q + (μ * (4 * (b : ℝ) / N)) ^ q ≤ 8 / (N : ℝ) ^ (p + 1) := by
    calc
      _ ≤ 2 * (2 * (N : ℝ) * (μ * (4 * V / N)) ^ q + (4 * μ ^ 2 * V / N) ^ q +
        (μ ^ 2 * (8 * V / N)) ^ q + (μ * (4 * (b : ℝ) / N)) ^ q) := by linarith only [hnonneg]
      _ ≤ 2 * (4 / (N : ℝ) ^ (p + 1)) := mul_le_mul_of_nonneg_left hbudget (by norm_num)
      _ = _ := by ring
  apply (hprob.trans hdouble).trans
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  apply (div_le_div_iff₀ (pow_pos hn _) (pow_pos hn _)).mpr
  rw [pow_succ]
  nlinarith [mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ N by exact_mod_cast hN)
    (pow_nonneg hn.le p)]

/-- The chosen nonresonant source radius also realizes the same count bound
on the actual offset auxiliary event; its radius comparison is derived. -/
theorem eventually_selected_sourceFullGeometricGood_probability (a d ω p : ℕ) (c γ : ℝ)
    (ha : 0 < a) (hd : 3 ≤ d) (hc : 0 < c) (hc₁ : c < 1) (hγ : γ < 1) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ᶠ N : ℕ in Filter.atTop,
      ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      offsetStructural (logarithmicRadius (c / 4) d N) ω 1 ⌊(N : ℝ) ^ γ⌋₊ g →
      eventMass (localSamplingWeight g.graph
        (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
        (fun S => ¬ SourceFullGeometricGood g.graph o (actualCavityDepth a d N z - 1)
          (logarithmicRadius (c / 4) d N) ω (q - 1) (q - 1)
          (2 * q * (2 * (q - 1) + 1)) (q - 1) S) ≤ 4 / (N : ℝ) ^ p := by
  obtain ⟨q, hq, hprob⟩ := eventually_sourceFullGeometricGood_probability a d ω p c γ hd hc hc₁ hγ
  have hr := (lowerLogLogRadius_tendsto a d ha hd).eventually (Filter.eventually_ge_atTop 4)
  refine ⟨q, hq, ?_⟩
  filter_upwards [hprob, hr] with N hprob hr
  intro g o z haux
  exact hprob g o _ (actualCavityDepth_radius_bounds a d N z hr).2 (haux.1 o) haux.2

end RegularGraph
end
end LocalLaw
