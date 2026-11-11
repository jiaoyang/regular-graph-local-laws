import LocalLaw.SourceFullFrozenComparison
import LocalLaw.SourceDeletedFrozenComparison
import LocalLaw.FirstStageFrozenProbability

/-! Both physical first-stage comparisons are proved, so the actual resampling
first-stage estimate has every polynomial probability exponent. -/
noncomputable section
namespace LocalLaw
local instance sourceFirstStageProofDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem source_first_stage_frozen_comparison_family (a b d:ℕ)(c β γ B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hB:0≤B):
    SourceFirstStageFrozenComparisonFamily a b d c β γ B:=by
  obtain ⟨Df,hDf,hfull⟩:=RegularGraph.source_full_frozen_comparison a b d c β B ha hb hd hc hβ hβc
  intro q hq
  let Bnear:=finiteOmega d+q
  let Dd:=sourceDeletedFrozenErrorConstant d β B Bnear
  refine ⟨Df,Dd,hDf,sourceDeletedFrozenErrorConstant_nonnegative d β B Bnear,?_⟩
  filter_upwards [hfull,
    RegularGraph.eventually_source_deleted_frozen_comparison a b d Bnear c β B ha hb hd hc hβ hβc hB]
    with N hFull hDeleted
  intro g o z hz hzB hfloor hoff hweak ι _ labels samples
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let R:=logarithmicRadius (c/4) d N
  let new:=g.labelledResampledGraph T labels samples (R/4)
  let badCount:=⌊(N:ℝ)^γ⌋₊
  have hsource:g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
      R (finiteOmega d) badCount z:=⟨RegularGraph.offsetStructural_implies_structural hoff,hweak⟩
  intro hgood
  have hnear:∀v:(Tᶜ:Set (Fin N)),(tripleNearIndices g.graph T (R/2) samples v).card≤Bnear:=by
    intro v
    exact (hgood.1.1 v).trans (by dsimp only[Bnear];omega)
  refine ⟨?_,?_⟩
  · exact hFull g o z hz hzB hfloor badCount hsource labels samples
  · exact hDeleted g o z badCount hz hzB hfloor hsource labels samples hnear

theorem source_first_stage_all_powers (a b d:ℕ)(c β γ B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hc1:c<1)(hβ:0<β)(hβc:β≤c/32)
    (hγ:c/4<γ)(hγ1:γ<1)(hB:0≤B):
    SourceFirstStageAllPowers a b d c β γ B:=
  sourceFirstStageAllPowers_of_frozen_comparisons a b d c β γ B ha hb hd hc hc1 hβ hβc hγ hγ1 hB
    (source_first_stage_frozen_comparison_family a b d c β γ B ha hb hd hc hβ hβc hB)

end LocalLaw
