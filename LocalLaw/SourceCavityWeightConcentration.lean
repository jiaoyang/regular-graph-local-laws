import LocalLaw.CavityWeightFamily
import LocalLaw.SourceCavityMinorProfile
import LocalLaw.SourceFixedWeightConcentration
import LocalLaw.GeometricKernelProbability

/-! # Actual concentration for all deterministic neighbor cavity weights -/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance sourceCavityWeightConcentrationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def cavityWeightL1Constant (d : ℕ) (β : ℝ) : ℝ :=
  8 * (d : ℝ) * finiteExtraReferenceConstant d ^ 2 * sourceObservationLogCap d β
def cavityWeightNoiseConstant (d : ℕ) (β : ℝ) : ℝ :=
  32 * (d : ℝ) * finiteExtraReferenceConstant d ^ 4 * sourceObservationLogCap d β + 1
def cavityWeightMaxConstant (d : ℕ) : ℝ := 4 * finiteExtraReferenceConstant d ^ 2

namespace RegularGraph
variable {N d : ℕ}

def SourceCavityWeightGood (g : RegularGraph N d) (a : ℕ) (c β C1 : ℝ) (o : Fin N) (z : ℂ)
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))) : Prop :=
  g.SourceFixedWeightGood a c β C1 (cavityWeightNoiseConstant d β) (cavityWeightL1Constant d β) o z
    (g.cavityMinorWeights o (actualCavityDepth a d N z - 1) (g.Q z) z) samples

theorem eventually_sourceCavityWeightGood_failure (a b d p : ℕ) (c β γ B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hγ : c / 4 < γ) (hgap : γ + β < 1)
    (hB : 0 ≤ B) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∀ Cq badCount : ℕ, badCount ≤ ⌊(N : ℝ) ^ γ⌋₊ →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1) (finiteOmega d) Cq badCount C1 o z →
      (graphBall g.graph o (actualCavityDepth a d N z - 1)).IsTree →
      eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
        (fun samples => ¬g.SourceCavityWeightGood a c β C1 o z samples) ≤ 1 / (N : ℝ) ^ p := by
  filter_upwards [eventually_source_cavity_minor_profile a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceFixedWeightGood_failure a b d p c β γ B C1
      (cavityWeightNoiseConstant d β) (cavityWeightL1Constant d β) ha hb hd hc hβ hβc hγ hgap hB hC1]
    with N hprofile hconcentration
  intro g o z hz hzB hfloor Cq badCount hbad hplus hTree
  obtain ⟨hell, hp⟩ := hprofile g o z hz hfloor Cq badCount hplus
  let ell := actualCavityDepth a d N z - 1
  have hell' : 2 ≤ ell := hell
  have hcaps (j : g.graph.neighborSet o) := (hp (g.cavityNeighborInBall o ell hell j) j.property.symm hTree).2
  have hl1 : ∀ j, ∑ α, ‖g.cavityMinorWeights o ell (g.Q z) z j α‖ ≤
      cavityWeightL1Constant d β * Real.log (N : ℝ) := by
    intro j
    simp only [cavityMinorWeights, dif_pos hell']
    exact (hcaps j).1
  have hl2 : ∀ j, Real.sqrt (∑ α, ‖g.cavityMinorWeights o ell (g.Q z) z j α‖ ^ 2) ≤
      cavityWeightNoiseConstant d β * Real.log (N : ℝ) / resamplingDecayDenominator d ell := by
    intro j
    simp only [cavityMinorWeights, dif_pos hell']
    exact (hcaps j).2.1
  exact hconcentration g o z hz hzB hfloor Cq badCount hbad hplus (g.graph.neighborSet o)
    (g.cavityNeighborFamily_card_le o) _ hl1 hl2

end RegularGraph

def ballSourceCavityWeightBad {N d : ℕ} (a : ℕ) (c β C1 : ℝ) (o : Fin N) (z : ℂ) : BallLabelledSpace N d → Prop :=
  ballCanonicalSampleEvent o (actualCavityDepth a d N z - 1)
    (fun g samples => ¬g.SourceCavityWeightGood a c β C1 o z samples)

theorem eventually_ballSourceCavityWeightBad_probability (a b d p : ℕ) (c β γ B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hγ : c / 4 < γ) (hgap : γ + β < 1)
    (hB : 0 ≤ B) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ∀ Cq : ℕ,
      eventMass (ballLabelledWeight N d o (actualCavityDepth a d N z - 1)) (fun ξ =>
        (ballLabelledProject ξ).SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
          (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1) (finiteOmega d) Cq ⌊(N : ℝ) ^ γ⌋₊ C1 o z ∧
        (graphBall (ballLabelledProject ξ).graph o (actualCavityDepth a d N z - 1)).IsTree ∧
        ballSourceCavityWeightBad a c β C1 o z ξ) ≤ 1 / (N : ℝ) ^ p := by
  filter_upwards [RegularGraph.eventually_sourceCavityWeightGood_failure a b d p c β γ B C1
    ha hb hd hc hβ hβc hγ hgap hB hC1] with N htail
  intro o z hz hzB hfloor Cq
  let ell := actualCavityDepth a d N z - 1
  let A : RegularGraph N d → Prop := fun g =>
    g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
      (logarithmicRadius (c / 4) d N) ell (finiteOmega d) Cq ⌊(N : ℝ) ^ γ⌋₊ C1 o z ∧
      (graphBall g.graph o ell).IsTree
  have h := ballCanonical_sample_failure_bound N d o ell A
    (fun g samples => ¬g.SourceCavityWeightGood a c β C1 o z samples) (1 / (N : ℝ) ^ p)
      (fun g hA => htail g o z hz hzB hfloor Cq _ le_rfl hA.1 hA.2)
  have hmass : eventMass (RegularGraph.weight (N := N) (d := d)) A ≤ 1 := finiteUniform_eventMass_le_one A
  have hbound := h.trans ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq (mul_one _))
  have hcover : ∀ ξ, ((ballLabelledProject ξ).SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β)
      (logarithmicRadius β d N) (logarithmicRadius (c / 4) d N) ell (finiteOmega d) Cq
      ⌊(N : ℝ) ^ γ⌋₊ C1 o z ∧ (graphBall (ballLabelledProject ξ).graph o ell).IsTree ∧
      ballSourceCavityWeightBad a c β C1 o z ξ) →
      A (ballLabelledProject ξ) ∧ ballCanonicalSampleEvent o ell
        (fun g samples => ¬g.SourceCavityWeightGood a c β C1 o z samples) ξ :=
    fun ξ hξ => ⟨⟨hξ.1, hξ.2.1⟩, hξ.2.2⟩
  exact (eventMass_mono (ballLabelledWeight N d o ell) (ballLabelledWeight_nonnegative N d o ell) hcover).trans hbound

end LocalLaw
