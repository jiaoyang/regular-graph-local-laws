import LocalLaw.FirstStageProbabilityPackaging
import LocalLaw.FirstStageBoundaryAssembly

/-! Only two frozen physical estimates remain in the first-stage contract.
All model boundary changes, event membership and probability losses are proved. -/
noncomputable section
namespace LocalLaw
local instance firstStageFrozenProbabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 3000000

def SourceFirstStageFrozenComparisonFamily (a b d : ℕ) (c β γ B : ℝ) : Prop :=
  ∀q:ℕ,1≤q→∃(Dfull Ddeleted:ℝ),1≤Dfull ∧ 0≤Ddeleted ∧
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      RegularGraph.offsetStructural (logarithmicRadius (c/4) d N) (finiteOmega d) 1 ⌊(N:ℝ)^γ⌋₊ g →
      (graphLocalLawFamilyWithRadii N d a (effectiveModelRadius a d N β) (logarithmicRadius β d N)).weak z g →
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      let R:=logarithmicRadius (c/4) d N
      SourceFullGeometricGood g.graph o ell R (finiteOmega d) (q-1) (q-1)
        (2*q*(2*(q-1)+1)) (q-1) samples →
      RegularGraph.FirstStageFrozenComparisons g (g.labelledResampledGraph T labels samples (R/4))
        T a (effectiveModelRadius a d N β) (logarithmicRadius β d N) z Dfull Ddeleted

theorem sourceFirstStage_comparison_family_of_frozen (a b d:ℕ)(c β γ B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)
    (hγ:c/4<γ)(hB:0≤B)
    (hphysical:SourceFirstStageFrozenComparisonFamily a b d c β γ B) :
    SourceFirstStageComparisonFamily a b d c β γ B := by
  intro q hq
  obtain ⟨Df,Dd,hDf,hDd,hfrozen⟩:=hphysical q hq
  refine ⟨Df,Dd,hDf,hDd,?_⟩
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [hfrozen,
    RegularGraph.eventually_firstStage_packet_of_frozen a b d (finiteOmega d+q) c β B Df Dd ha hb hd hc hβ hβc hB hDf,
    RegularGraph.eventually_resampling_badCenter_cost a d c γ hd hc.le hγ,
    eventually_resampling_radius_margin a d 2 2 (c/4) hd (by linarith),hdepth]
    with N hphysicalN hpacket hcost hmargin hdepthN
  intro g o z hz hzB hfloor hoff hweak ι _ labels samples
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let R:=logarithmicRadius (c/4) d N
  let badCount:=⌊(N:ℝ)^γ⌋₊
  let Cq:=resamplingLargeExcessConstant d (finiteOmega d) (q-1) (q-1)
    (2*q*(2*(q-1)+1)) (q-1)
  intro hgood
  have hsource:g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
      R (finiteOmega d) badCount z:=⟨RegularGraph.offsetStructural_implies_structural hoff,hweak⟩
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hfit:2*ell+2≤R:=by dsimp only [R]; omega
  have hstruct:=g.structural_sourceFullGood_labelledResampled_structuralPlus o ell R (finiteOmega d)
    (q-1) (q-1) (2*q*(2*(q-1)+1)) (q-1) badCount hd hfit labels samples hsource.1
    (hcost g o ell hell) hgood
  have hnear:∀v:(Tᶜ:Set (Fin N)),(tripleNearIndices g.graph T (R/2) samples v).card≤finiteOmega d+q:=by
    intro v
    exact (hgood.1.1 v).trans (by omega)
  exact hpacket g o z hz hzB hfloor badCount Cq hsource labels samples hstruct hnear
    (hphysicalN g o z hz hzB hfloor hoff hweak labels samples hgood)

theorem sourceFirstStageAllPowers_of_frozen_comparisons (a b d:ℕ)(c β γ B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hc1:c<1)(hβ:0<β)(hβc:β≤c/32)
    (hγ:c/4<γ)(hγ1:γ<1)(hB:0≤B)
    (hphysical:SourceFirstStageFrozenComparisonFamily a b d c β γ B) :
    SourceFirstStageAllPowers a b d c β γ B :=
  sourceFirstStageAllPowers_of_comparison_family a b d c β γ B ha hb hd hc hc1 hβ hβc hγ hγ1 hB
    (sourceFirstStage_comparison_family_of_frozen a b d c β γ B ha hb hd hc hβ hβc hγ hB hphysical)
end LocalLaw
