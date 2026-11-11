import LocalLaw.SingletonObservationBudgets
import LocalLaw.SourceSingletonGeometry
import LocalLaw.IndependentRadiusEvents

/-!
# The actual bounded observation in source (6.4)

The source event supplies the scalar prior and the four deleted pair-model
approximations. A genuine adjacent-endpoint common ball supplies the finite
reference model. Every kernel, pivot and localization estimate is derived.
The nominal error radius is independent of the internal model radius.
-/

noncomputable section
namespace LocalLaw
local instance sourceSingletonObservationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def singletonObservationDiameter (d r : ℕ) : ℕ :=
  (finiteOmega d + 1) * (4 * (r + 1) + 1)

/-- Explicit finite numerical conditions, subsequently realizable from the
source logarithmic scales. No observation or Green estimate is a field. -/
structure SourceObservationBounds (d r : ℕ) (z : ℂ) (B C ε L A : ℝ) : Prop where
  error_nonnegative : 0 ≤ ε
  log_one : 1 ≤ L
  log_cap_nonnegative : 0 ≤ A
  coefficient_one : 1 ≤ C
  error_scaled : (C ^ 2 * ε) * L ^ 4 ≤ 1
  diameter_log : ((singletonObservationDiameter d r : ℕ) : ℝ) + 1 ≤ A * L
  pair_log : ((4 * r + 1 : ℕ) + 1 : ℝ) ≤ A * L
  localization_large : DeficientGraph.localizationBudgetConstant d B A ≤ L
  feedback_large : DeficientGraph.localizationWeakConstant d B A * C ≤ L ^ 2
  pivot_large : 4 * DeficientGraph.singletonPivotConstant d B ≤ L
  tail : physicalTransfer d z ^ (2 * r) ≤ C ^ 2 * ε

namespace RegularGraph
variable {N d : ℕ}

/-- Source (6.4) for the genuine singleton-deleted graph, with every
finite-model estimate and scalar pivot smallness discharged. -/
theorem source_singleton_observation_of_bounds (g : RegularGraph N d)
    (a rModel rError R ell Cq badCount : ℕ) (C1 B A : ℝ) (o : Fin N) (z : ℂ)
    (h : g.SourceOmegaPlusWithRadii a rModel rError R ell (finiteOmega d) Cq badCount C1 o z)
    (hd : 3 ≤ d) (hz : 0 < z.im) (hB : ‖z‖ ≤ B)
    (S : SourceObservationBounds d rModel z B C1
      (graphPaperError a d N rError z) (Real.log (N : ℝ)) A)
    (hmargin : rModel + 1 ≤ R / 8) (hfarMargin : rModel + 2 ≤ R / 4)
    (b c : ((graphBallVertices g.graph o ell)ᶜ : Set (Fin N)))
    (hbc : (outsideGraph g.graph (graphBallVertices g.graph o ell)).Adj b c)
    (hfar : ∀ α : BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell),
      ((R / 4 : ℕ) : ℕ∞) < (outsideGraph g.graph (graphBallVertices g.graph o ell)).edist b
        (boundaryOuterEndpoint g.graph (graphBallVertices g.graph o ell) α)) :
    let D := g.deficient.delete (graphBallVertices g.graph o ell)
    ‖(D.deleteVertex b).G z ⟨c, hbc.ne.symm⟩ ⟨c, hbc.ne.symm⟩ -
      (D.deleteVertex b).P rModel z (g.Q z) ⟨c, hbc.ne.symm⟩ ⟨c, hbc.ne.symm⟩‖ ≤
        DeficientGraph.singletonObservationConstant d * C1 * g.sourcePrime a rError z := by
  let T := graphBallVertices g.graph o ell
  let D := g.deficient.delete T
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N rError z
  let δ := C1 * L ^ 3 * ε
  have hC1 : 0 ≤ C1 := (by norm_num : (0 : ℝ) ≤ 1).trans S.coefficient_one
  have hL0 : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 1).trans S.log_one
  have hδ : 0 ≤ δ := by dsimp only [δ]; exact mul_nonneg (mul_nonneg hC1 (pow_nonneg hL0 _)) S.error_nonnegative
  have hprior : ‖g.Q z - semicircleRoot z‖ ≤ C1 * scalarScale (spectralScale z) ε := h.cavity
  have hpriorScaled := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) S.error_nonnegative S.coefficient_one)
  have hscaled : 0 ≤ C1 ^ 2 * ε := mul_nonneg (sq_nonneg C1) S.error_nonnegative
  have hbudgets := DeficientGraph.singleton_observation_source_budgets d hd z (g.Q z) hz B ε L A C1
    hB S.error_nonnegative S.log_one S.log_cap_nonnegative S.coefficient_one S.error_scaled
    hprior S.feedback_large S.pivot_large
  have hfar' : ∀ α : BoundaryOrientedEdge g.graph T,
      ((rModel + 2 : ℕ) : ℕ∞) < (outsideGraph g.graph T).edist b (boundaryOuterEndpoint g.graph T α) := by
    intro α
    exact lt_of_le_of_lt (by exact_mod_cast hfarMargin) (hfar α)
  have hconditions := g.singleton_common_ball_reference_conditions T b c hbc rModel (R / 8)
    hmargin h.structural.1 hfar'
  have happ (x y : (Tᶜ : Set (Fin N))) : ‖D.G z x y - D.P rModel z (g.Q z) x y‖ ≤ δ := by
    have hδeq : δ = C1 * g.sourcePrime a rError z := by
      dsimp only [δ, L, ε, sourcePrime, inflatedPrime]
      ring
    rw [hδeq]
    exact h.deleted x y
  have hobs := D.common_ball_singleton_observation hd b c hbc rModel hconditions.1 hconditions.2
    (g.Q z) z hz (g.Q_im_nonnegative z hz) B hB (C1 ^ 2 * ε) L A δ hscaled hδ
    S.log_one S.log_cap_nonnegative S.error_scaled hpriorScaled
    (singletonObservationDiameter d rModel) (Nat.le_refl _) S.diameter_log S.pair_log
    S.localization_large S.tail (happ c c) (happ c b) (happ b c) (happ b b) hbudgets.1
  apply hobs.trans
  apply hbudgets.2.trans_eq
  change DeficientGraph.singletonObservationConstant d * (C1 * L ^ 3 * ε) = _
  change _ = DeficientGraph.singletonObservationConstant d * C1 * (L ^ 3 * ε)
  ring

/-- The literal masked observation Z of source Section 6.1. Its input is
one actual uniformly sampled oriented edge outside T. -/
def sourceSingletonObservation (g : RegularGraph N d) (T : Set (Fin N)) (r farRadius : ℕ)
    (z q : ℂ) (e : OutsideOrientedEdge g.graph T) : ℂ :=
  let b : (Tᶜ : Set (Fin N)) := ⟨e.val.1, e.property.2.1⟩
  let c : (Tᶜ : Set (Fin N)) := ⟨e.val.2, e.property.2.2⟩
  let hbc : (outsideGraph g.graph T).Adj b c := e.property.1
  let D := g.deficient.delete T
  if ∀ α : BoundaryOrientedEdge g.graph T,
      (farRadius : ℕ∞) < (outsideGraph g.graph T).edist b (boundaryOuterEndpoint g.graph T α) then
    (D.deleteVertex b).G z ⟨c, hbc.ne.symm⟩ ⟨c, hbc.ne.symm⟩ -
      (D.deleteVertex b).P r z q ⟨c, hbc.ne.symm⟩ ⟨c, hbc.ne.symm⟩
  else 0

/-- The actual source observable is uniformly bounded on every edge in the
sampling fiber; the far-boundary mask is part of its definition. -/
theorem sourceSingletonObservation_bound (g : RegularGraph N d)
    (a rModel rError R ell Cq badCount : ℕ) (C1 B A : ℝ) (o : Fin N) (z : ℂ)
    (h : g.SourceOmegaPlusWithRadii a rModel rError R ell (finiteOmega d) Cq badCount C1 o z)
    (hd : 3 ≤ d) (hz : 0 < z.im) (hB : ‖z‖ ≤ B)
    (S : SourceObservationBounds d rModel z B C1
      (graphPaperError a d N rError z) (Real.log (N : ℝ)) A)
    (hmargin : rModel + 1 ≤ R / 8) (hfarMargin : rModel + 2 ≤ R / 4)
    (e : OutsideOrientedEdge g.graph (graphBallVertices g.graph o ell)) :
    ‖g.sourceSingletonObservation (graphBallVertices g.graph o ell) rModel (R / 4) z (g.Q z) e‖ ≤
      DeficientGraph.singletonObservationConstant d * C1 * g.sourcePrime a rError z := by
  let T := graphBallVertices g.graph o ell
  let b : (Tᶜ : Set (Fin N)) := ⟨e.val.1, e.property.2.1⟩
  let c : (Tᶜ : Set (Fin N)) := ⟨e.val.2, e.property.2.2⟩
  let hbc : (outsideGraph g.graph T).Adj b c := e.property.1
  change ‖if (∀ α : BoundaryOrientedEdge g.graph T,
      ((R / 4 : ℕ) : ℕ∞) < (outsideGraph g.graph T).edist b (boundaryOuterEndpoint g.graph T α)) then
      ((g.deficient.delete T).deleteVertex b).G z ⟨c, hbc.ne.symm⟩ ⟨c, hbc.ne.symm⟩ -
        ((g.deficient.delete T).deleteVertex b).P rModel z (g.Q z) ⟨c, hbc.ne.symm⟩ ⟨c, hbc.ne.symm⟩
    else 0‖ ≤ _
  by_cases hfar : ∀ α : BoundaryOrientedEdge g.graph T,
      ((R / 4 : ℕ) : ℕ∞) < (outsideGraph g.graph T).edist b (boundaryOuterEndpoint g.graph T α)
  · have hh := g.source_singleton_observation_of_bounds a rModel rError R ell Cq badCount C1 B A o z
      h hd hz hB S hmargin hfarMargin b c hbc hfar
    rw [if_pos hfar]
    exact hh
  · rw [if_neg hfar, norm_zero]
    have hC : 0 ≤ DeficientGraph.singletonObservationConstant d := by
      unfold DeficientGraph.singletonObservationConstant
      positivity
    have hC1 : 0 ≤ C1 := (by norm_num : (0 : ℝ) ≤ 1).trans S.coefficient_one
    have hL0 : 0 ≤ Real.log (N : ℝ) := (by norm_num : (0 : ℝ) ≤ 1).trans S.log_one
    change 0 ≤ DeficientGraph.singletonObservationConstant d * C1 *
      (Real.log (N : ℝ) ^ 3 * graphPaperError a d N rError z)
    exact mul_nonneg (mul_nonneg hC hC1)
      (mul_nonneg (pow_nonneg hL0 _) S.error_nonnegative)

end RegularGraph
end LocalLaw
