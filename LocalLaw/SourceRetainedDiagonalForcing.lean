import LocalLaw.SourceRetainedWeightGood
import LocalLaw.ActualFixedWeightLeading
import LocalLaw.ActualSourceResidualTransport
import LocalLaw.SourceBoundaryDiagonal
import LocalLaw.SourceSurgeryGoodCounts
import LocalLaw.WeightedDiagonalDefect

/-! # Actual complete diagonal forcing for an inside row -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceRetainedDiagonalForcingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceRetainedDiagonalConstant (d J : ℕ) (β C1 : ℝ) : ℝ :=
  let A1 := sourceRetainedWeightL1Constant d β
  let Cnoise := sourceRetainedWeightNoiseConstant d β
  let W := sourceRetainedWeightMaxConstant d
  let V := 22 + 2 * (finiteOmega d : ℝ) + (J : ℝ)
  actualFixedWeightLeadingConstant d C1 Cnoise A1 V W + A1 + sourceEndpointErrorConstant d C1 * V * W

def sourceRetainedDiagonalFeedbackConstant (d : ℕ) (β B : ℝ) : ℝ :=
  sourceRetainedWeightL1Constant d β * sourceResidualFeedbackConstant d β B

namespace RegularGraph

theorem eventually_source_retained_diagonal_forcing (a b d J : ℕ) (c β γ B C1 : ℝ) (Cq : ℕ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hγ : c / 4 < γ) (hgap : γ + β < 1)
    (hB : 0 ≤ B) (hC1 : 1 ≤ C1)
    (hCdel : sourceDeletionConstant d β B ≤ C1) (hCq : finiteOmega d ≤ Cq) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∀ badCount : ℕ, badCount ≤ ⌊(N : ℝ) ^ γ⌋₊ →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let ell := actualCavityDepth a d N z - 1
      let R := logarithmicRadius (c / 4) d N
      let T := graphBallVertices g.graph o ell
      let r := effectiveModelRadius a d N β
      let L := Real.log (N : ℝ)
      let ε := graphPaperError a d N (logarithmicRadius β d N) z
      let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
      let gnew := g.labelledResampledGraph T labels samples (R / 4)
      let D := g.sourceBoundaryDefect T labels samples (R / 4) r (g.Q z) z
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) R (finiteOmega d) badCount z →
      ¬g.sourceGreenIsolationBad T z φ (R / 4) (Nat.ceil L) samples →
      (rejectedResamplingIndices g.graph T (R / 4) samples).card ≤ J →
      g.SourceRetainedWeightGood a c β C1 o z samples → ∀ y : T,
      ‖∑ i, g.sourceRetainedProductWeights o ell r (g.Q z) z y (labels i) * D i i‖ ≤
        sourceRetainedDiagonalConstant d J β C1 * (ε / L ^ 4) +
          sourceRetainedDiagonalFeedbackConstant d β B * L ^ 2 * gnew.sourceFeedback z := by
  let A1 := sourceRetainedWeightL1Constant d β
  let Cnoise := sourceRetainedWeightNoiseConstant d β
  let W := sourceRetainedWeightMaxConstant d
  let Vbad : ℝ := 22 + 2 * (finiteOmega d : ℝ) + (J : ℝ)
  let K := actualFixedWeightLeadingConstant d C1 Cnoise A1 Vbad W
  let D0 := sourceEndpointErrorConstant d C1
  let Kres := sourceResidualFeedbackConstant d β B
  have hA := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hA1 : 0 ≤ A1 := by dsimp only [A1,sourceRetainedWeightL1Constant]; positivity
  have hnoise : 0 ≤ Cnoise := by dsimp only [Cnoise,sourceRetainedWeightNoiseConstant]; positivity
  have hW : 0 ≤ W := by dsimp only [W,sourceRetainedWeightMaxConstant]; positivity
  have hVbad : 0 ≤ Vbad := by dsimp only [Vbad]; positivity
  have hC10 : 0 ≤ C1 := (by norm_num : (0 : ℝ) ≤ 1).trans hC1
  have hK : 0 ≤ K := by dsimp only [K,actualFixedWeightLeadingConstant,DeficientGraph.singletonObservationConstant]; positivity
  have hD0 : 0 ≤ D0 := by dsimp only [D0,sourceEndpointErrorConstant]; positivity
  filter_upwards [eventually_actual_fixed_weight_leading a b d c β γ B C1 Cnoise A1 Vbad W Cq
      ha hb hd hc hβ hβc hγ hgap hB hC1 hnoise hA1 hVbad hW hCdel hCq,
    eventually_source_retained_product_weight_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_source_residual_transport a b d c β B C1 ha hb hd hc hβ hβc hC1 hB,
    eventually_actual_boundary_defect_pattern a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1]
    with N hforce hweights hresidual hpattern hmargin hnum
  intro g o z hz hzB hfloor badCount hbadCount hplus ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let R := logarithmicRadius (c/4) d N
  let T := graphBallVertices g.graph o ell
  let r := effectiveModelRadius a d N β
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
  let s := g.admissibleState T labels samples
  let gnew := g.labelledResampledGraph T labels samples (R/4)
  let D := g.sourceBoundaryDefect T labels samples (R/4) r (g.Q z) z
  let w := g.sourceRetainedProductWeights o ell r (g.Q z) z
  let Y := cavityIterate z (g.Q z) (r+1)
  let δ := D0 * g.sourcePrime a (logarithmicRadius β d N) z
  intro htarget hisolation hrejected hconcentration y
  have num := hnum z hz hfloor
  have hε : 0 ≤ ε := num.error_nonnegative
  have hL : 1 ≤ L := num.log_one
  have hLp : 0 < L := by linarith
  have hφ : 0 ≤ φ := by dsimp only [φ,correlationThreshold]; positivity
  have hpweights := hweights g o z hz hfloor Cq badCount hplus
  obtain ⟨hfit,hpat⟩ := hpattern g o z hz hfloor hzB Cq badCount hplus labels samples
  have hp := hpat φ hφ
  let good := g.sourceSurgeryGoodIndices o ell R hfit labels z φ samples
  have hbad : ((Finset.univ \ good).card : ℝ) ≤ Vbad * L ^ 2 :=
    g.sourceSurgeryGoodIndices_bad_log_bound o ell R (finiteOmega d) J hfit (hplus.structural.1 o)
      labels z φ samples hL hisolation hrejected
  have hproperties (i : ι) (hi : i ∈ good) := g.sourceSurgeryGoodLabels_properties o ell R hfit z φ
    samples (labels i) (Finset.mem_filter.mp hi).2
  have heligible : ∀ i ∈ good, s.Eligible (R/4) i := fun i hi => (Finset.mem_filter.mp (hproperties i hi).2.2).2
  have hcorrelation : ∀ i ∈ good, labels i ∈ g.sourceCorrelationGoodLabels T z φ (R/4) samples :=
    fun i hi => (hproperties i hi).1
  have hleading := hforce g o z hz hzB hfloor badCount hbadCount hplus T w
    (fun y => (hpweights y).1) (fun y => (hpweights y).2.2)
    labels samples badCount htarget good heligible hcorrelation hbad hconcentration y
  have hsep : 2*r+2≤R/4 := by dsimp only [r,R]; omega
  have hr : r+2≤R/4 := by dsimp only [r,R]; omega
  have hDgood : ∀ i ∈ good, D i i =
      (gnew.deficient.delete T).G z (s.sampledOutsideSecond i).val (s.sampledOutsideSecond i).val - Y :=
    fun i hi => g.sourceBoundaryDefect_eligible_diagonal hd T labels samples (R/4) r hsep hr
      (g.Q z) z hz (g.Q_im_nonnegative z hz) i (heligible i hi)
  have hl1 : (∑ i, ‖w y (labels i)‖) ≤ A1 * L := by
    rw [labels.sum_comp (fun α => ‖w y α‖)]
    exact (hpweights y).1
  have hgain : L^9≤resamplingDecayDenominator d ell := selected_radius_decay_gain a d N z ha hd hL
  have hmax : ∀ i ∉ good, ‖w y (labels i)‖≤W/L^9 := by
    intro i _
    exact ((hpweights y).2.2 (labels i)).trans (div_le_div_of_nonneg_left hW (pow_pos hLp 9) hgain)
  have hδ : 0≤δ := by dsimp only [δ,sourcePrime,inflatedPrime]; positivity
  have htransfer := weighted_diagonal_defect_transfer good (fun i => w y (labels i)) (fun i => D i i)
    (fun i => (gnew.deficient.delete T).G z (s.sampledOutsideSecond i).val (s.sampledOutsideSecond i).val)
    Y (g.Q z) (K*(ε/L^4)) (A1*L) δ (W/L^9)
    (by positivity) (by positivity) hδ (by positivity) hDgood hleading hl1 (fun i => hp.1 i i) hmax
  have hres := hresidual g o z hz hzB hfloor Cq badCount hplus labels samples htarget
  have hresMul := mul_le_mul_of_nonneg_right hres (show 0≤A1*L by positivity)
  have hbadTerm : δ * ((Finset.univ \ good).card : ℝ) * (W/L^9) ≤ D0*Vbad*W*(ε/L^4) := by
    calc
      _ ≤ δ*(Vbad*L^2)*(W/L^9) := by gcongr
      _ = _ := by dsimp only [δ,sourcePrime,inflatedPrime]; field_simp; ring
  have htail : (ε/L^8)*(A1*L) ≤ A1*(ε/L^4) := by
    have hh := div_le_div_of_nonneg_left hε (pow_pos hLp 5) (pow_le_pow_right₀ hL (show 5≤8 by omega))
    have hh := mul_le_mul_of_nonneg_right hh (show 0≤A1*L by positivity)
    apply hh.trans_eq
    field_simp
    ring
  apply htransfer.trans
  change K*(ε/L^4)+‖g.Q z-Y‖*(A1*L)+δ*((Finset.univ\good).card:ℝ)*(W/L^9) ≤ _
  dsimp only [sourceRetainedDiagonalConstant,sourceRetainedDiagonalFeedbackConstant]
  change _ ≤ (K+A1+D0*Vbad*W)*(ε/L^4)+(A1*Kres)*L^2*gnew.sourceFeedback z
  nlinarith only [hresMul,hbadTerm,htail]

end RegularGraph
end LocalLaw
