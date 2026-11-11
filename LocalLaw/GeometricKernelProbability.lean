import LocalLaw.ResamplingProbabilityLift
import LocalLaw.GeometricSamplingParameters

/-!
# The geometric good event in the actual reversible kernel

A canonical chosen-ball sample event is transported along the proved chosen
vertex-set equality. Uniform boundary labels are marginalized by the exact
kernel disintegration. The resulting F1 failure bound is on BallLabelledSpace,
which is the same enlarged space used by the local-law bootstrap.
-/

namespace LocalLaw
noncomputable section
local instance geometricKernelDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A canonical ball sample predicate on any auxiliary fixed-T state. -/
def canonicalBallSamplePredicate {N d : ℕ} (o : Fin N) (ell : ℕ)
    (P : ∀ g : RegularGraph N d, LocalSamplingFiber g.graph (graphBallVertices g.graph o ell) → Prop)
    (T : Set (Fin N)) (g : RegularGraph N d) (S : LocalSamplingFiber g.graph T) : Prop :=
  ∀ h : graphBallVertices g.graph o ell = T, P g (h.symm ▸ S)

/-- At the actual chosen ball, transport along its equality has no effect. -/
theorem canonicalBallSamplePredicate_self {N d : ℕ} (o : Fin N) (ell : ℕ)
    (P : ∀ g : RegularGraph N d, LocalSamplingFiber g.graph (graphBallVertices g.graph o ell) → Prop)
    (g : RegularGraph N d) (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) :
    canonicalBallSamplePredicate o ell P (graphBallVertices g.graph o ell) g S ↔ P g S := by
  constructor
  · intro h
    exact h rfl
  · intro h heq
    cases heq
    exact h

def ballCanonicalSampleEvent {N d : ℕ} (o : Fin N) (ell : ℕ)
    (P : ∀ g : RegularGraph N d, LocalSamplingFiber g.graph (graphBallVertices g.graph o ell) → Prop) :
    BallLabelledSpace N d → Prop := ballLabelledSampleEvent (canonicalBallSamplePredicate o ell P)

/-- Every pointwise chosen-ball sample estimate holds in the actual enlarged
kernel with its original graph base-event factor. -/
theorem ballCanonical_sample_failure_bound (N d : ℕ) (o : Fin N) (ell : ℕ)
    (A : RegularGraph N d → Prop)
    (P : ∀ g : RegularGraph N d, LocalSamplingFiber g.graph (graphBallVertices g.graph o ell) → Prop)
    (δ : ℝ) (hP : ∀ g, A g →
      eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o ell)) (P g) ≤ δ) :
    eventMass (ballLabelledWeight N d o ell)
      (fun ω => A (ballLabelledProject ω) ∧ ballCanonicalSampleEvent o ell P ω) ≤
        δ * eventMass RegularGraph.weight A := by
  apply ballLabelled_sample_failure_bound N d o ell A (canonicalBallSamplePredicate o ell P) δ
  intro g hA
  have heq : canonicalBallSamplePredicate o ell P (graphBallVertices g.graph o ell) g = P g := by
    funext S
    exact propext (canonicalBallSamplePredicate_self o ell P g S)
  rw [heq]
  exact hP g hA

/-- The failure of the actual source geometric sampling event, expressed on
the exact graph-dependent ball-labelled resampling space. -/
def ballGeometricBad {N d : ℕ} (o : Fin N) (ell R ω q : ℕ) : BallLabelledSpace N d → Prop :=
  ballCanonicalSampleEvent o ell (fun g S => ¬SourceGeometricGood g.graph o ell R ω
    (q - 1) (q - 1) (2 * q * (2 * (q - 1) + 1)) (q - 1) S)

/-- The genuine resampling kernel has an arbitrary polynomial F1 failure
bound, uniformly in the center and the selected spectral radius. -/
theorem eventually_ballGeometricBad_probability (a d ω p : ℕ) (c γ : ℝ)
    (ha : 0 < a) (hd : 3 ≤ d) (hc : 0 < c) (hc₁ : c < 1) (hγ : γ < 1) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ᶠ N : ℕ in Filter.atTop, ∀ (o : Fin N) (z : ℂ),
      eventMass (ballLabelledWeight N d o (actualCavityDepth a d N z - 1)) (fun ξ =>
        RegularGraph.offsetStructural (logarithmicRadius (c / 4) d N) ω 1 ⌊(N : ℝ) ^ γ⌋₊
          (ballLabelledProject ξ) ∧
        ballGeometricBad o (actualCavityDepth a d N z - 1) (logarithmicRadius (c / 4) d N) ω q ξ) ≤
          4 / (N : ℝ) ^ p := by
  obtain ⟨q, hq, hprob⟩ := RegularGraph.eventually_selected_sourceGeometricGood_probability
    a d ω p c γ ha hd hc hc₁ hγ
  refine ⟨q, hq, ?_⟩
  filter_upwards [hprob] with N hprob
  intro o z
  let A : RegularGraph N d → Prop := RegularGraph.offsetStructural
    (logarithmicRadius (c / 4) d N) ω 1 ⌊(N : ℝ) ^ γ⌋₊
  have hbound := ballCanonical_sample_failure_bound N d o (actualCavityDepth a d N z - 1)
    A (fun g S => ¬SourceGeometricGood g.graph o (actualCavityDepth a d N z - 1)
      (logarithmicRadius (c / 4) d N) ω (q - 1) (q - 1)
      (2 * q * (2 * (q - 1) + 1)) (q - 1) S) (4 / (N : ℝ) ^ p)
    (fun g hA => hprob g o z hA)
  have hmass : eventMass (RegularGraph.weight (N := N) (d := d)) A ≤ 1 :=
    finiteUniform_eventMass_le_one A
  exact hbound.trans ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq (mul_one _))

end
end LocalLaw
