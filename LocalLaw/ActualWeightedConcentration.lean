import LocalLaw.BoundaryWeightParameters
import LocalLaw.BoundaryConcentrationFamily

/-!
# Concentration with the actual Green-product source weights

The independent outside-edge sampling law is combined with the proved
incidence, decay and logarithmic weight estimates. The only observation
inputs are its actual boundedness and true one-edge bias. No weight norm,
independence, MGF, tail estimate or union cost is assumed.
-/

open scoped BigOperators NNReal
noncomputable section
namespace LocalLaw
local instance actualWeightedConcentrationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem boundaryProductWeight_concentration (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hbudget : (g.restrict S).ComponentFiniteReferenceBudget)
    (o : V) (ell : ℕ) (hS : graphBallVertices g.graph o ell ⊆ S)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (R : ℕ)
    (hR : ∀ a b, (g.restrict S).graph.dist a b ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2)
    (A L : ℝ) (hA : 0 ≤ A) (hL : 1 ≤ L) (hRlog : (R : ℝ) + 1 ≤ A * L)
    (hout : Nonempty (OutsideOrientedEdge g.graph (graphBallVertices g.graph o ell)))
    (Z : OutsideOrientedEdge g.graph (graphBallVertices g.graph o ell) → ℂ)
    (b : ℝ≥0) (hb : 0 < b) (hbound : ∀ e, ‖Z e‖ ≤ (b : ℝ))
    (target : ℂ) (δ : ℝ) (hδ : 0 ≤ δ) (hbias : ‖finiteComplexMean Z - target‖ ≤ δ) :
    eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o ell))
      (fun samples => ∃ i : S,
        (32 * (d : ℝ) * finiteExtraReferenceConstant d ^ 4 * A + 1) * L ^ 2 * b /
            resamplingDecayDenominator d ell +
          δ * (8 * (d : ℝ) * finiteExtraReferenceConstant d ^ 2 * A) * L <
        ‖∑ a, g.boundaryProductWeight S o ell hS q z i a * (Z (samples a) - target)‖) ≤
      (Nat.card S : ℝ) * (4 * Real.exp (-L ^ 2 / 32)) := by
  let T := graphBallVertices g.graph o ell
  let w : S → BoundaryOrientedEdge g.graph T → ℂ := g.boundaryProductWeight S o ell hS q z
  have hfamily := localSampling_weighted_family_concentration g.graph T hout
    (fun _ e => Z e) (fun _ => target) w Finset.univ b hb (fun _ _ e => hbound e) δ
    (fun _ _ => hbias) L (by linarith)
  simp only [Nat.card_eq_fintype_card] at hfamily ⊢
  apply (eventMass_mono _ finiteUniformWeight_nonneg ?_).trans hfamily
  intro samples hsamples
  obtain ⟨i, hi⟩ := hsamples
  refine ⟨i, ?_⟩
  obtain ⟨hl1, hl2, _⟩ := g.boundaryProductWeight_log_bounds hd S hbudget o ell hS q z hz hq R hR small A L hA hL hRlog i
  have hnoise := mul_le_mul_of_nonneg_left hl2 (show 0 ≤ L * (b : ℝ) by positivity)
  have hbias' := mul_le_mul_of_nonneg_left hl1 hδ
  have hthreshold : L * b * Real.sqrt (∑ a, ‖w i a‖ ^ 2) + δ * (∑ a, ‖w i a‖) ≤
      (32 * (d : ℝ) * finiteExtraReferenceConstant d ^ 4 * A + 1) * L ^ 2 * b /
          resamplingDecayDenominator d ell +
        δ * (8 * (d : ℝ) * finiteExtraReferenceConstant d ^ 2 * A) * L := by
    convert add_le_add hnoise hbias' using 1
    ring
  exact lt_of_le_of_lt hthreshold hi

end DeficientGraph
end LocalLaw
