import LocalLaw.SourceDeletedModelComparison
import LocalLaw.ActualAugmentedSurgery
import LocalLaw.SourceOmegaPlusTransferEffective

/-! # Actual physical switched deleted Green comparison at the old boundary

The original weak event supplies the enlarged old event through the proved
source deletion implication. Actual F1 occupancy then gives augmented surgery,
and the literal pair model is recovered by the proved finite-star comparison.
-/

open Filter
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance sourceDeletedFrozenDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceDeletedFrozenC1 (d:ℕ)(β B:ℝ):ℝ:=1+|sourceDeletionConstant d β B|

def sourceDeletedFrozenErrorConstant (d:ℕ)(β B:ℝ)(Bnear:ℕ):ℝ:=
  augmentedSurgeryErrorConstant d (sourceDeletedFrozenC1 d β B) Bnear+
    sourceDeletedModelErrorConstant d β B (sourceDeletedFrozenC1 d β B)

theorem sourceDeletedFrozenC1_ge_one (d:ℕ)(β B:ℝ) : 1≤sourceDeletedFrozenC1 d β B:=by
  unfold sourceDeletedFrozenC1
  linarith [abs_nonneg (sourceDeletionConstant d β B)]

theorem sourceDeletedFrozenC1_ge_deletion (d:ℕ)(β B:ℝ) :
    sourceDeletionConstant d β B≤sourceDeletedFrozenC1 d β B:=by
  unfold sourceDeletedFrozenC1
  linarith [le_abs_self (sourceDeletionConstant d β B)]

theorem sourceDeletedFrozenErrorConstant_nonnegative (d:ℕ)(β B:ℝ)(Bnear:ℕ) :
    0≤sourceDeletedFrozenErrorConstant d β B Bnear:=by
  unfold sourceDeletedFrozenErrorConstant augmentedSurgeryErrorConstant sourceDeletedModelErrorConstant
    sourceDeletedFrozenC1 sourceInnerStarPrimeConstant sourceInnerStarHarmonicRow
    sourceInnerStarHarmonicError sourceInnerStarCoreMain sourceInnerStarCoreCap
  positivity

namespace RegularGraph

theorem eventually_source_deleted_frozen_comparison (a b d Bnear:ℕ)(c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hB:0≤B) :
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ)(badCount:ℕ),
      0<z.im→‖z‖≤B→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let R:=logarithmicRadius (c/4) d N
      let selector:=R/4
      let r:=effectiveModelRadius a d N β
      let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
      (∀v:(Tᶜ:Set (Fin N)),(tripleNearIndices g.graph T (R/2) samples v).card≤Bnear)→
      ∀x y:(Tᶜ:Set (Fin N)),‖new.G z x y-new.P r z (g.Q z) x y‖≤
        sourceDeletedFrozenErrorConstant d β B Bnear*g.sourcePrime a (logarithmicRadius β d N) z := by
  let C1:=sourceDeletedFrozenC1 d β B
  have hC1:1≤C1:=sourceDeletedFrozenC1_ge_one d β B
  have hCdel:sourceDeletionConstant d β B≤C1:=sourceDeletedFrozenC1_ge_deletion d β B
  filter_upwards [eventually_sourceOmegaWithRadii_subset_sourceOmegaPlusWithRadii a b d c β B C1 (finiteOmega d)
      ha hb hd hc hβ hβc hB hC1 hCdel (le_refl _),
    eventually_actual_augmented_surgery a b d Bnear c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_deleted_model_comparison a b d c β B C1 ha hb hd hc hβ hβc hC1]
    with N hplus haug hmodel
  intro g o z badCount hz hzB hfloor hsource ι _ labels samples
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let R:=logarithmicRadius (c/4) d N
  let selector:=R/4
  let r:=effectiveModelRadius a d N β
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  let s:=g.admissibleState T labels samples
  intro hnear x y
  let S:=s.twoTargetEndpointVertices selector r x y
  let xl:S:=twoBallLeft (outsideGraph g.graph T) (s.endpointModelVertices selector r) x y r
  let yl:S:=twoBallRight (outsideGraph g.graph T) (s.endpointModelVertices selector r) x y r
  have hp:=hplus g o z badCount hz hzB hfloor hsource
  have hstrong:=hsource.1.1
  have hΨ:0≤scalarScale (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z):=
    (norm_nonneg _).trans hsource.2.1
  have hprior:‖g.Q z-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
      (graphPaperError a d N (logarithmicRadius β d N) z):=
    hsource.2.1.trans (le_mul_of_one_le_left hΨ hC1)
  have ha':=haug g o z hz hfloor hzB (finiteOmega d) badCount hp hstrong labels samples hnear x y
  have hm:=hmodel g o z (g.Q z) hz hzB hfloor (g.Q_im_nonnegative z hz) hprior hstrong labels samples x y
  have ht:=norm_sub_le_norm_sub_add_norm_sub (new.G z x y)
    ((new.restrict S).extensionGreen (g.Q z) z xl yl) (new.P r z (g.Q z) x y)
  exact (ht.trans (add_le_add ha' hm)).trans_eq (by
    unfold sourceDeletedFrozenErrorConstant
    ring)

end RegularGraph
end LocalLaw
