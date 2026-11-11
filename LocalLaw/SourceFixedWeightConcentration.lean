import LocalLaw.SourceObservationConcentration

/-! # Actual source concentration for a deterministic weight family -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceFixedWeightConcentrationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

def SourceFixedWeightGood (g : RegularGraph N d) (a : ℕ) (c β C1 Cnoise A1 : ℝ)
    (o : Fin N) (z : ℂ) {J : Type} [Fintype J]
    (w : J → BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)) → ℂ)
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))) : Prop :=
  let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let D := resamplingDecayDenominator d (actualCavityDepth a d N z - 1)
  let amp := DeficientGraph.singletonObservationConstant d * C1 * g.sourcePrime a (logarithmicRadius β d N) z
  ∀ j, ‖∑ α, w j α * (g.sourceSingletonObservation T (effectiveModelRadius a d N β)
      (logarithmicRadius (c / 4) d N / 4) z (g.Q z) (samples α) -
        (g.Q z - cavityIterate z (g.Q z) (effectiveModelRadius a d N β + 1)))‖ ≤
    Cnoise * L ^ 2 * amp / D + (3 * ε / L ^ 16) * A1 * L

theorem eventually_sourceFixedWeightGood_failure (a b d q : ℕ) (c β γ B C1 Cnoise A1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hγ : c / 4 < γ) (hgap : γ + β < 1)
    (hB : 0 ≤ B) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∀ Cq badCount : ℕ, badCount ≤ ⌊(N : ℝ) ^ γ⌋₊ →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ (J : Type) [Fintype J], Fintype.card J ≤ N →
      ∀ w : J → BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)) → ℂ,
      (∀ j, ∑ α, ‖w j α‖ ≤ A1 * Real.log (N : ℝ)) →
      (∀ j, Real.sqrt (∑ α, ‖w j α‖ ^ 2) ≤ Cnoise * Real.log (N : ℝ) /
        resamplingDecayDenominator d (actualCavityDepth a d N z - 1)) →
      eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
        (fun samples => ¬g.SourceFixedWeightGood a c β C1 Cnoise A1 o z w samples) ≤ 1 / (N : ℝ) ^ q := by
  filter_upwards [eventually_sourceSingletonObservation_concentration a b d q c β γ B C1
    ha hb hd hc hβ hβc hγ hgap hB hC1,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1]
    with N hconc hnum
  intro g o z hz hzB hfloor Cq badCount hbad hplus J _ hJ w hl1 hl2
  have hsource := hconc g o z hz hzB hfloor Cq badCount hbad hplus J hJ w
  apply (eventMass_mono _ finiteUniformWeight_nonneg ?_).trans hsource
  intro samples hfailure
  unfold SourceFixedWeightGood at hfailure
  dsimp only at hfailure
  push_neg at hfailure
  obtain ⟨j, hj⟩ := hfailure
  refine ⟨j, ?_⟩
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let amp := DeficientGraph.singletonObservationConstant d * C1 * g.sourcePrime a (logarithmicRadius β d N) z
  have num := hnum z hz hfloor
  have hL : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 1).trans num.log_one
  have hamp : 0 ≤ amp := by
    have hC : 0 ≤ C1 := (by norm_num : (0 : ℝ) ≤ 1).trans hC1
    change 0 ≤ DeficientGraph.singletonObservationConstant d * C1 *
      (L ^ 3 * graphPaperError a d N (logarithmicRadius β d N) z)
    have he := num.error_nonnegative
    unfold DeficientGraph.singletonObservationConstant
    positivity
  have hε : 0 ≤ ε := num.error_nonnegative
  have hh1 := mul_le_mul_of_nonneg_left (hl2 j) (mul_nonneg hL hamp)
  have hh2 := mul_le_mul_of_nonneg_left (hl1 j) (show 0 ≤ 3 * ε / L ^ 16 by positivity)
  have hthreshold : L * amp * Real.sqrt (∑ α, ‖w j α‖ ^ 2) +
      (3 * ε / L ^ 16) * (∑ α, ‖w j α‖) ≤
      Cnoise * L ^ 2 * amp / resamplingDecayDenominator d (actualCavityDepth a d N z - 1) +
        (3 * ε / L ^ 16) * A1 * L := by
    convert add_le_add hh1 hh2 using 1
    ring
  exact lt_of_le_of_lt hthreshold hj

end RegularGraph
end LocalLaw
