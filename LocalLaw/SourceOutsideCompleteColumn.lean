import LocalLaw.ActualOutsideColumnGood
import LocalLaw.SourceSurgeryGoodCounts
import LocalLaw.OmegaPlusHalfGeometry

/-! # Every actual outside-column counting premise is discharged

The canonical eligible/correlation-good labels and the actual half-radius
geometric event supply all finite counts. Uniform external correlation is
kept as its separately proved sampling event.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance sourceOutsideCompleteColumnDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceOutsideCompleteColumnConstant (d J Cq qGeo : ℕ) (B C1 : ℝ) : ℝ :=
  sourceOutsideColumnErrorConstant d B C1 (22+2*(finiteOmega d:ℝ)+(J:ℝ))
    (RegularGraph.halfGeometryOccupancyConstant Cq qGeo)

theorem sourceOutsideCompleteColumnConstant_nonnegative (d J Cq qGeo : ℕ) (B C1 : ℝ)
    (hd : 3≤d) (hB : 0≤B) (hC1 : 0≤C1) :
    0≤sourceOutsideCompleteColumnConstant d J Cq qGeo B C1 := by
  have hP : 0≤sourceGreenPivotCap d B := by
    unfold sourceGreenPivotCap
    have hh := finiteReferenceConstant_ge_one d hd
    positivity
  have hC : 0≤guardedGreenEntryCap d := by
    dsimp only [guardedGreenEntryCap,commonGreenEntryCap]
    have hh := finiteExtraReferenceConstant_ge_one d hd
    linarith
  have hw : 0≤endpointSurgeryCouplingCap d := by unfold endpointSurgeryCouplingCap; positivity
  dsimp only [sourceOutsideCompleteColumnConstant,sourceOutsideColumnErrorConstant,sourceGoodExternalColumnConstant]
  positivity

namespace RegularGraph

theorem eventually_sourceOutsideColumnGood_complete (a b d J qGeo : ℕ) (c β B C1 : ℝ) (Cq : ℕ)
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
      g.SourceOutsideColumnGood a c β (sourceOutsideCompleteColumnConstant d J Cq qGeo B C1) o z labels samples := by
  let Kbad : ℝ := 22+2*(finiteOmega d:ℝ)+(J:ℝ)
  let Knear : ℝ := halfGeometryOccupancyConstant Cq qGeo
  have hKbad : 0≤Kbad := by dsimp only [Kbad]; positivity
  have hKnear : 0≤Knear := Nat.cast_nonneg _
  filter_upwards [eventually_sourceOutsideColumnGood_of_counts a b d c β B C1 Kbad Knear Cq
      ha hb hd hc hβ hβc hB hC1 hCdel hCq hKbad hKnear,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_log_ge_nat 1] with N hcolumns hmargin hlog
  intro g o z hz hzB hfloor badCount hplus ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let T := graphBallVertices g.graph o ell
  let R := logarithmicRadius (c/4) d N
  let r := effectiveModelRadius a d N β
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
  let s := g.admissibleState T labels samples
  intro htarget hisolation hrejected hcorr hgeometry
  have hfit : ell+1≤R/8 := by have hh := hmargin.2.2.2 z; dsimp only [ell,R]; omega
  let good := g.sourceSurgeryGoodIndices o ell R hfit labels z φ samples
  have hgood : ∀ i∈good,s.Eligible (R/4) i ∧ labels i∈g.sourceCorrelationGoodLabels T z φ (R/4) samples := by
    intro i hi
    have hp := g.sourceSurgeryGoodLabels_properties o ell R hfit z φ samples (labels i) (Finset.mem_filter.mp hi).2
    exact ⟨(Finset.mem_filter.mp hp.2.2).2,hp.1⟩
  have hbad : ((Finset.univ\good).card:ℝ)≤Kbad*L^2 :=
    g.sourceSurgeryGoodIndices_bad_log_bound o ell R (finiteOmega d) J hfit (hplus.structural.1 o)
      labels z φ samples hlog hisolation hrejected
  have hnear := g.halfGeometricGood_switched_occupancy o ell R Cq qGeo labels samples hgeometry
  have hnear' (x : (Tᶜ:Set (Fin N))) :
      ((tripleNearIndices (s.fullResample (R/4)).graph T (R/4) (s.fullResample (R/4)).samples x).card:ℝ)≤Knear*L :=
    (Nat.cast_le.mpr (hnear x)).trans (le_mul_of_one_le_right hKnear hlog)
  exact hcolumns g o z hz hzB hfloor badCount hplus labels samples htarget good hgood hbad hcorr hnear'

end RegularGraph
end LocalLaw
