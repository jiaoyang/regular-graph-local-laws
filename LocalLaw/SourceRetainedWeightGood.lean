import LocalLaw.SourceRetainedProductWeights

/-! # Genuine polynomial tail for all fixed retained row-product weights -/

noncomputable section
namespace LocalLaw
local instance sourceRetainedWeightGoodDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceRetainedWeightL1Constant (d : ℕ) (β : ℝ) : ℝ :=
  8 * (d : ℝ) * finiteExtraReferenceConstant d ^ 2 * sourceObservationLogCap d β

def sourceRetainedWeightNoiseConstant (d : ℕ) (β : ℝ) : ℝ :=
  32 * (d : ℝ) * finiteExtraReferenceConstant d ^ 4 * sourceObservationLogCap d β + 1

def sourceRetainedWeightMaxConstant (d : ℕ) : ℝ := 4 * finiteExtraReferenceConstant d ^ 2

namespace RegularGraph
variable {N d : ℕ}

def SourceRetainedWeightGood (g : RegularGraph N d) (a : ℕ) (c β C1 : ℝ) (o : Fin N) (z : ℂ)
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))) : Prop :=
  g.SourceFixedWeightGood a c β C1 (sourceRetainedWeightNoiseConstant d β)
    (sourceRetainedWeightL1Constant d β) o z
    (g.sourceRetainedProductWeights o (actualCavityDepth a d N z - 1) (effectiveModelRadius a d N β) (g.Q z) z) samples

theorem eventually_sourceRetainedWeightGood_failure (a b d q : ℕ) (c β γ B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hγ : c / 4 < γ) (hgap : γ + β < 1)
    (hB : 0 ≤ B) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∀ Cq badCount : ℕ, badCount ≤ ⌊(N : ℝ) ^ γ⌋₊ →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
        (fun samples => ¬g.SourceRetainedWeightGood a c β C1 o z samples) ≤ 1 / (N : ℝ) ^ q := by
  filter_upwards [eventually_sourceFixedWeightGood_failure a b d q c β γ B C1
      (sourceRetainedWeightNoiseConstant d β) (sourceRetainedWeightL1Constant d β)
      ha hb hd hc hβ hβc hγ hgap hB hC1,
    eventually_source_retained_product_weight_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1]
    with N htail hweights
  intro g o z hz hzB hfloor Cq badCount hbad hplus
  have hprofile := hweights g o z hz hfloor Cq badCount hplus
  have hcard : Fintype.card (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)) ≤ N := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))
  exact htail g o z hz hzB hfloor Cq badCount hbad hplus _ hcard _
    (fun y => (hprofile y).1) (fun y => (hprofile y).2.1)

end RegularGraph
end LocalLaw
