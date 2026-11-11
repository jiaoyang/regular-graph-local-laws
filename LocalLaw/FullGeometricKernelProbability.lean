import LocalLaw.FullGeometricParameters
import LocalLaw.GeometricKernelProbability

/-!
# The strengthened geometric event under the actual reversible kernel

The extra own-label collision control is retained in the actual chosen-ball
labelled space used by the bootstrap. Uniform labels and graph-dependent
sample fibers are marginalized by the proved kernel disintegration.
-/

namespace LocalLaw
noncomputable section
local instance fullGeometricKernelDecidable (p : Prop) : Decidable p := Classical.propDecidable p
def ballFullGeometricBad {N d : ℕ} (o : Fin N) (ell R ω q : ℕ) : BallLabelledSpace N d → Prop :=
  ballCanonicalSampleEvent o ell (fun g S => ¬SourceFullGeometricGood g.graph o ell R ω
    (q - 1) (q - 1) (2 * q * (2 * (q - 1) + 1)) (q - 1) S)

/-- The genuine resampling kernel has an arbitrary polynomial F1 failure
bound, uniformly in the center and the selected spectral radius. -/
theorem eventually_ballFullGeometricBad_probability (a d ω p : ℕ) (c γ : ℝ)
    (ha : 0 < a) (hd : 3 ≤ d) (hc : 0 < c) (hc₁ : c < 1) (hγ : γ < 1) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ᶠ N : ℕ in Filter.atTop, ∀ (o : Fin N) (z : ℂ),
      eventMass (ballLabelledWeight N d o (actualCavityDepth a d N z - 1)) (fun ξ =>
        RegularGraph.offsetStructural (logarithmicRadius (c / 4) d N) ω 1 ⌊(N : ℝ) ^ γ⌋₊
          (ballLabelledProject ξ) ∧
        ballFullGeometricBad o (actualCavityDepth a d N z - 1) (logarithmicRadius (c / 4) d N) ω q ξ) ≤
          4 / (N : ℝ) ^ p := by
  obtain ⟨q, hq, hprob⟩ := RegularGraph.eventually_selected_sourceFullGeometricGood_probability
    a d ω p c γ ha hd hc hc₁ hγ
  refine ⟨q, hq, ?_⟩
  filter_upwards [hprob] with N hprob
  intro o z
  let A : RegularGraph N d → Prop := RegularGraph.offsetStructural
    (logarithmicRadius (c / 4) d N) ω 1 ⌊(N : ℝ) ^ γ⌋₊
  have hbound := ballCanonical_sample_failure_bound N d o (actualCavityDepth a d N z - 1)
    A (fun g S => ¬SourceFullGeometricGood g.graph o (actualCavityDepth a d N z - 1)
      (logarithmicRadius (c / 4) d N) ω (q - 1) (q - 1)
      (2 * q * (2 * (q - 1) + 1)) (q - 1) S) (4 / (N : ℝ) ^ p)
    (fun g hA => hprob g o z hA)
  have hmass : eventMass (RegularGraph.weight (N := N) (d := d)) A ≤ 1 :=
    finiteUniform_eventMass_le_one A
  exact hbound.trans ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq (mul_one _))

end
end LocalLaw
