import LocalLaw.OmegaPlusRejectionProbability
import LocalLaw.GeometricKernelProbability
import LocalLaw.IndependentRadiusEvents

/-! # Actual Omega-plus rejected-label probability in the reversible kernel -/

noncomputable section
namespace LocalLaw
local instance omegaPlusRejectedKernelDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def ballSourceRejectedBad {N d : ℕ} (o : Fin N) (ell R Cq q : ℕ) : BallLabelledSpace N d → Prop :=
  ballCanonicalSampleEvent o ell (fun g S => sourceRejectionConstant Cq q <
    (rejectedResamplingIndices g.graph (graphBallVertices g.graph o ell) (R / 4) S).card)

theorem eventually_ballSourceRejectedBad_probability (a d p : ℕ) (c γ : ℝ)
    (ha : 0 < a) (hd : 3 ≤ d) (hc : 0 < c) (hc₁ : c < 1) (hγ : γ < 1) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ᶠ N : ℕ in Filter.atTop, ∀ (o : Fin N) (z : ℂ)
      (rModel rError ω Cq : ℕ) (C1 : ℝ),
      eventMass (ballLabelledWeight N d o (actualCavityDepth a d N z - 1)) (fun ξ =>
        (ballLabelledProject ξ).SourceOmegaPlusWithRadii a rModel rError
          (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1) ω Cq
          ⌊(N : ℝ) ^ γ⌋₊ C1 o z ∧
        ballSourceRejectedBad o (actualCavityDepth a d N z - 1)
          (logarithmicRadius (c / 4) d N) Cq q ξ) ≤ 1 / (N : ℝ) ^ p := by
  obtain ⟨q, hq, hprob⟩ := RegularGraph.eventually_structuralPlus_rejection_probability a d p c γ hd hc hc₁ hγ
  have hr := (lowerLogLogRadius_tendsto a d ha hd).eventually (Filter.eventually_ge_atTop 4)
  refine ⟨q, hq, ?_⟩
  filter_upwards [hprob, hr] with N hprob hr
  intro o z rModel rError ω Cq C1
  let ell := actualCavityDepth a d N z - 1
  let R := logarithmicRadius (c / 4) d N
  let A : RegularGraph N d → Prop := fun g =>
    g.SourceOmegaPlusWithRadii a rModel rError R ell ω Cq ⌊(N : ℝ) ^ γ⌋₊ C1 o z
  let P := fun (g : RegularGraph N d) (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) =>
    sourceRejectionConstant Cq q < (rejectedResamplingIndices g.graph (graphBallVertices g.graph o ell) (R / 4) S).card
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hr).2
  have hbound := ballCanonical_sample_failure_bound N d o ell A P (1 / (N : ℝ) ^ p)
    (fun g hA => hprob g o ell ω Cq hell hA.structural)
  have hmass : eventMass (RegularGraph.weight (N := N) (d := d)) A ≤ 1 :=
    finiteUniform_eventMass_le_one A
  exact hbound.trans ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq (mul_one _))

end LocalLaw
