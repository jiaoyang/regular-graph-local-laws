import LocalLaw.SourceCorrelationProbability
import LocalLaw.GeometricKernelProbability

/-! # The actual source F2 probability in the chosen-ball kernel

The local correlation estimate is integrated through the proved exact sample
disintegration. Retained boundary labels and graph-dependent ball choices
therefore introduce no missing probability-transfer premise.
-/

noncomputable section
namespace LocalLaw

local instance sourceCorrelationKernelDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def ballSourceCorrelationBad {N d : ℕ} (o : Fin N) (ell a rError R : ℕ) (z : ℂ) :
    BallLabelledSpace N d → Prop :=
  ballCanonicalSampleEvent o ell (fun g S =>
    let T := graphBallVertices g.graph o ell
    ∃ x : {w : Fin N // w ∉ T}, Nat.ceil (Real.log (N : ℝ)) ≤
      (g.correlatedSampleIndices T z
        (correlationThreshold (Real.log (N : ℝ)) a N z.im
          (graphKestenMcKayReference d z).im (spectralScale z) (graphPaperError a d N rError z))
        (R / 4) x S).card)

theorem eventually_ballSourceCorrelationBad_probability
    (a b d q : ℕ) (c β C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d)
    (hc : 0 < c) (hc₁ : c < 1) (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 0 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ∀ Cq badCount : ℕ,
      eventMass (ballLabelledWeight N d o (actualCavityDepth a d N z - 1)) (fun ξ =>
        (ballLabelledProject ξ).SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β)
          (logarithmicRadius β d N) (logarithmicRadius (c / 4) d N)
          (actualCavityDepth a d N z - 1) (finiteOmega d) Cq badCount C1 o z ∧
        ballSourceCorrelationBad o (actualCavityDepth a d N z - 1) a (logarithmicRadius β d N)
          (logarithmicRadius (c / 4) d N) z ξ) ≤ 1 / (N : ℝ) ^ q := by
  filter_upwards [eventually_sourceOmegaPlusWithRadii_few_correlated_samples a b d q c β C1
    ha hb hd hc hc₁ hβ hβc hC1] with N htail
  intro o z hz hscale Cq badCount
  let ell := actualCavityDepth a d N z - 1
  let R := logarithmicRadius (c / 4) d N
  let rn := logarithmicRadius β d N
  let A : RegularGraph N d → Prop := fun g =>
    g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) rn R ell (finiteOmega d) Cq badCount C1 o z
  let P := fun (g : RegularGraph N d) (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) =>
    let T := graphBallVertices g.graph o ell
    ∃ x : {w : Fin N // w ∉ T}, Nat.ceil (Real.log (N : ℝ)) ≤
      (g.correlatedSampleIndices T z
        (correlationThreshold (Real.log (N : ℝ)) a N z.im
          (graphKestenMcKayReference d z).im (spectralScale z) (graphPaperError a d N rn z))
        (R / 4) x S).card
  have hbound := ballCanonical_sample_failure_bound N d o ell A P (1 / (N : ℝ) ^ q)
    (fun g hA => htail g o z hz hscale Cq badCount hA)
  have hmass : eventMass (RegularGraph.weight (N := N) (d := d)) A ≤ 1 :=
    finiteUniform_eventMass_le_one A
  exact hbound.trans ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq (mul_one _))

end LocalLaw
