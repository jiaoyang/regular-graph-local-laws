import LocalLaw.SourceInsideReferenceRow
import LocalLaw.SourceInsidePairCorrection

/-! # Actual improved inside row against the switched pair reference

This combines the exact fixed-reference Schur expansion with the derived
finite pair-model correction. All geometric and analytic estimates come
from the actual source and retained target events and the proved sampling
good events.
-/

noncomputable section
namespace LocalLaw
local instance sourceInsideRowDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceInsideBaseConstant (d J : ℕ) (β C1 : ℝ) : ℝ :=
  sourceInsideReferenceBaseConstant d J β C1+2

def sourceInsideFeedbackConstant (d : ℕ) (β B : ℝ) : ℝ :=
  sourceRetainedDiagonalFeedbackConstant d β B+sourceInsidePairFeedbackConstant d β B

namespace RegularGraph

theorem eventually_source_inside_row (a b d J : ℕ) (c β γ B C1 : ℝ) (Cq : ℕ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hγ : c/4<γ) (hgap : γ+β<1)
    (hB : 0≤B) (hC1 : 1≤C1)
    (hCdel : sourceDeletionConstant d β B≤C1) (hCq : finiteOmega d≤Cq) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      ∀ badCount : ℕ,badCount≤⌊(N:ℝ)^γ⌋₊ →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell := actualCavityDepth a d N z-1
      let R := logarithmicRadius (c/4) d N
      let T := graphBallVertices g.graph o ell
      let r := effectiveModelRadius a d N β
      let L := Real.log (N:ℝ)
      let ε := graphPaperError a d N (logarithmicRadius β d N) z
      let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
      let gnew := g.labelledResampledGraph T labels samples (R/4)
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) R (finiteOmega d) badCount z →
      ¬g.sourceGreenIsolationBad T z φ (R/4) (Nat.ceil L) samples →
      (rejectedResamplingIndices g.graph T (R/4) samples).card≤J →
      g.SourceRetainedWeightGood a c β C1 o z samples → ∀ y : T,
      ‖gnew.G z o y.val-gnew.P r z (gnew.Q z) o y.val‖≤
        sourceInsideBaseConstant d J β C1*(ε/L^2)+
          sourceInsideFeedbackConstant d β B*L^2*gnew.sourceFeedback z := by
  have hA : 0≤filledEndpointLogCap d β := by
    have hh := sourceObservationLogCap_nonnegative d hd β hβ.le
    dsimp only [filledEndpointLogCap]; linarith
  have hconv := coreConvolutionConstant_nonnegative (finiteOmega d+1)
  have hK : 0≤sourceInsidePairFeedbackConstant d β B := by
    dsimp only [sourceInsidePairFeedbackConstant,DeficientGraph.localizationFeedbackConstant]
    positivity
  filter_upwards [eventually_source_inside_reference_row a b d J c β γ B C1 Cq
      ha hb hd hc hβ hβc hγ hgap hB hC1 hCdel hCq,
    eventually_source_inside_pair_correction a b d c β B C1 ha hb hd hc hβ hβc hC1 hB,
    eventually_log_ge_nat 1] with N hrow hpair hlog
  intro g o z hz hzB hfloor badCount hbad hplus ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let R := logarithmicRadius (c/4) d N
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let gnew := g.labelledResampledGraph T labels samples (R/4)
  let root : T := ⟨o,center_mem_graphBall g.graph o ell⟩
  intro htarget hisolation hrejected hweights y
  have hr := hrow g o z hz hzB hfloor badCount hbad hplus labels samples htarget hisolation hrejected hweights y
  have hp := hpair g o z hz hzB hfloor Cq badCount hplus labels samples htarget root y
  have hF : 0≤gnew.sourceFeedback z := by dsimp only [sourceFeedback]; positivity
  have hLL : L≤L^2 := by nlinarith only [sq_nonneg (L-1),hlog]
  have hfeedback : sourceInsidePairFeedbackConstant d β B*L*gnew.sourceFeedback z≤
      sourceInsidePairFeedbackConstant d β B*L^2*gnew.sourceFeedback z :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLL hK) hF
  have htriangle := norm_sub_le_norm_sub_add_norm_sub (gnew.G z o y.val)
    (g.sourceRetainedReference T r (g.Q z) z root y) (gnew.P r z (gnew.Q z) o y.val)
  apply htriangle.trans
  apply (add_le_add hr hp).trans
  dsimp only [sourceInsideBaseConstant,sourceInsideFeedbackConstant]
  nlinarith only [hfeedback]

end RegularGraph
end LocalLaw
