import LocalLaw.SourceCavityWeightConcentration
import LocalLaw.ActualFixedWeightLeading

/-! # Actual epsilon/log^4 diagonal forcing for every cavity neighbor

The deterministic weights are the genuine old truncated-T neighbor-minor
weights. Their profiles and their named concentration event are proved in
the companion modules; no full-model weight is substituted here.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance actualCavityDiagonalLeadingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def actualCavityLeadingConstant (d : ℕ) (β C1 Kbad : ℝ) : ℝ :=
  actualFixedWeightLeadingConstant d C1 (cavityWeightNoiseConstant d β) (cavityWeightL1Constant d β)
    Kbad (cavityWeightMaxConstant d)

namespace RegularGraph

theorem eventually_actual_cavity_diagonal_leading (a b d : ℕ) (c β γ B C1 Kbad : ℝ) (Cq : ℕ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hγ : c / 4 < γ) (hgap : γ + β < 1)
    (hB : 0 ≤ B) (hC1 : 1 ≤ C1) (hbad : 0 ≤ Kbad)
    (hCdel : sourceDeletionConstant d β B ≤ C1) (hCq : finiteOmega d ≤ Cq) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∀ badCount : ℕ, badCount ≤ ⌊(N : ℝ) ^ γ⌋₊ →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      (graphBall g.graph o (actualCavityDepth a d N z - 1)).IsTree →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let ell := actualCavityDepth a d N z - 1
      let T := graphBallVertices g.graph o ell
      let selector := logarithmicRadius (c / 4) d N / 4
      let s := g.admissibleState T labels samples
      let gnew := g.labelledResampledGraph T labels samples selector
      let L := Real.log (N : ℝ)
      let ε := graphPaperError a d N (logarithmicRadius β d N) z
      let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
      ∀ targetBadCount : ℕ,
      gnew.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (finiteOmega d) targetBadCount z →
      ∀ good : Finset ι,
      (∀ i ∈ good, s.Eligible selector i) →
      (∀ i ∈ good, labels i ∈ g.sourceCorrelationGoodLabels T z φ selector samples) →
      ((Finset.univ \ good).card : ℝ) ≤ Kbad * L ^ 2 →
      g.SourceCavityWeightGood a c β C1 o z samples →
      ∀ j : g.graph.neighborSet o,
      ‖∑ i ∈ good, g.cavityMinorWeights o ell (g.Q z) z j (labels i) *
        ((gnew.deficient.delete T).G z (s.sampledOutsideSecond i).val (s.sampledOutsideSecond i).val - g.Q z)‖ ≤
        actualCavityLeadingConstant d β C1 Kbad * (ε / L ^ 4) := by
  have hA := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hnoise : 0 ≤ cavityWeightNoiseConstant d β := by unfold cavityWeightNoiseConstant; positivity
  have hA1 : 0 ≤ cavityWeightL1Constant d β := by unfold cavityWeightL1Constant; positivity
  have hW : 0 ≤ cavityWeightMaxConstant d := by unfold cavityWeightMaxConstant; positivity
  filter_upwards [eventually_source_cavity_minor_profile a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_fixed_weight_leading a b d c β γ B C1 (cavityWeightNoiseConstant d β)
      (cavityWeightL1Constant d β) Kbad (cavityWeightMaxConstant d) Cq ha hb hd hc hβ hβc hγ hgap
      hB hC1 hnoise hA1 hbad hW hCdel hCq] with N hprofile hleading
  intro g o z hz hzB hfloor badCount hbadCount hplus hTree
  obtain ⟨hell, hp⟩ := hprofile g o z hz hfloor Cq badCount hplus
  let ell := actualCavityDepth a d N z - 1
  have hell' : 2 ≤ ell := hell
  have hw (j : g.graph.neighborSet o) := (hp (g.cavityNeighborInBall o ell hell j) j.property.symm hTree).2
  have hl1 : ∀ j, ∑ α, ‖g.cavityMinorWeights o ell (g.Q z) z j α‖ ≤
      cavityWeightL1Constant d β * Real.log (N : ℝ) := by
    intro j
    simp only [cavityMinorWeights, dif_pos hell']
    exact (hw j).1
  have hmax : ∀ j α, ‖g.cavityMinorWeights o ell (g.Q z) z j α‖ ≤
      cavityWeightMaxConstant d / resamplingDecayDenominator d ell := by
    intro j α
    simp only [cavityMinorWeights, dif_pos hell']
    exact (hw j).2.2 α
  intro ι _ labels samples
  dsimp only
  intro targetBadCount target good heligible hcorrelation hbadCard hconcentration j
  exact hleading g o z hz hzB hfloor badCount hbadCount hplus (g.graph.neighborSet o)
    (g.cavityMinorWeights o ell (g.Q z) z) hl1 hmax labels samples targetBadCount target good
    heligible hcorrelation hbadCard hconcentration j

end RegularGraph
end LocalLaw
