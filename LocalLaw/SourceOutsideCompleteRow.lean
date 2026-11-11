import LocalLaw.SourceOutsideCompleteColumn

/-! # Actual outside row with every finite counting input discharged -/

noncomputable section
namespace LocalLaw
local instance sourceOutsideCompleteRowDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceOutsideCompleteRowBase (d J Cq qGeo : ℕ) (β B C1 : ℝ) : ℝ :=
  sourceOutsideRowBaseConstant d J β C1 (sourceOutsideCompleteColumnConstant d J Cq qGeo B C1)

namespace RegularGraph

theorem eventually_source_outside_row_complete (a b d J qGeo : ℕ) (c β B C1 : ℝ) (Cq : ℕ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c) (hβ : 0<β) (hβc : β≤c/32)
    (hB : 0≤B) (hC1 : 1≤C1) (hCdel : sourceDeletionConstant d β B≤C1) (hCq : finiteOmega d≤Cq) :
    ∀ᶠ N : ℕ in Filter.atTop,∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell := actualCavityDepth a d N z-1
      let T := graphBallVertices g.graph o ell
      let R := logarithmicRadius (c/4) d N
      let r := effectiveModelRadius a d N β
      let L := Real.log (N:ℝ)
      let ε := graphPaperError a d N (logarithmicRadius β d N) z
      let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
      let gnew := g.labelledResampledGraph T labels samples (R/4)
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) R (finiteOmega d) badCount z →
      ¬g.sourceGreenIsolationBad T z φ (R/4) (Nat.ceil L) samples →
      (rejectedResamplingIndices g.graph T (R/4) samples).card≤J →
      (∀ x : (Tᶜ:Set (Fin N)),(g.correlatedSampleIndices T z φ (R/4) x samples).card≤Nat.ceil L) →
      SourceFullGeometricGood g.graph o ell (R/2) Cq (qGeo-1) (qGeo-1)
        (2*qGeo*(2*(qGeo-1)+1)) (qGeo-1) samples →
      ∀ y∉T,‖gnew.G z o y-gnew.P r z (gnew.Q z) o y‖≤
        sourceOutsideCompleteRowBase d J Cq qGeo β B C1*ε/L+
          sourceOutsideRowFeedbackConstant d β B*L^2*gnew.sourceFeedback z := by
  let Eout := sourceOutsideCompleteColumnConstant d J Cq qGeo B C1
  have hC10 : 0≤C1 := (by norm_num : (0:ℝ)≤1).trans hC1
  have hEout : 0≤Eout := sourceOutsideCompleteColumnConstant_nonnegative d J Cq qGeo B C1 hd hB hC10
  filter_upwards [eventually_sourceOutsideColumnGood_complete a b d J qGeo c β B C1 Cq
      ha hb hd hc hβ hβc hB hC1 hCdel hCq,
    eventually_source_outside_row_from_column a b d J c β B C1 Eout
      ha hb hd hc hβ hβc hC1 hB hEout] with N hcol hrow
  intro g o z hz hzB hfloor badCount hplus ι _ labels samples
  dsimp only
  intro htarget hisolation hrejected hcorr hgeometry
  have hc := hcol g o z hz hzB hfloor badCount hplus labels samples htarget hisolation hrejected hcorr hgeometry
  exact hrow g o z hz hzB hfloor Cq badCount hplus labels samples htarget hisolation hrejected hc

end RegularGraph
end LocalLaw
