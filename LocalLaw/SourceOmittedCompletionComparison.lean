import LocalLaw.ActualOmittedCompletionComparison
import LocalLaw.SourceOmittedKeptLeafDecay
import LocalLaw.OmittedKeptShiftedDistances
import LocalLaw.CanonicalOmittedIdentification

/-! # Actual source asymmetric completion comparison for the switched minor

The conclusion uses the literal switched restricted model after its actual
retained selected-B deletion. Every common-model row, kept-leaf decay,
normalization and omitted-root distance input is derived. The original
pair centers may themselves be selected B vertices.
-/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4500000
namespace LocalLaw
local instance sourceOmittedCompletionComparisonDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_omitted_completion_comparison (a b d : ℕ)(c β Bcap C1 : ℝ)
    (ha : 12≤a)(hb : 25*a≤b)(hd : 3≤d)(hc : 0<c)(hβ : 0<β)(hβc : β≤c/32)(hC1 : 1≤C1) :
    ∀ᶠ N:ℕ in atTop,∀(g : RegularGraph N d)(o : Fin N)(z q : ℂ),
      0<z.im → ‖z‖≤Bcap → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → 0≤q.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀{ι:Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : ((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      let S:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
      let W:=s.selectedFirstSet selector
      let Bi:=s.partialFirstRemovedSet selector S
      let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
      let e:=restrictionDeletionGraphIso new.graph S W Bi (fun _=>Iff.rfl)
      let J:=s.OmittedOrdinaryLeaves selector S⊕s.OmittedExtraLeaves selector S
      let A:=omittedCompletionObservationLogCap d β
      let L:=Real.log (N:ℝ)
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      let KM:=leafDeletedMateRowCap d Bcap
      let KA:=leafDeletedSeparatedRowCap d Bcap
      letI:DecidableEq (s.OmittedCore selector S):=fun a b=>Classical.propDecidable (a=b)
      ∀i j:(Biᶜ:Set S),∀ri rj:ℕ,ri≤r → rj≤r →
        (outsideGraph (s.fullResample selector).graph T).edist x i.val.val≤((r-ri:ℕ):ℕ∞) →
        (outsideGraph (s.fullResample selector).graph T).edist y j.val.val≤((r-rj:ℕ):ℕ∞) →
        let ai:=omittedRestoredSpatialConstant d Bcap A*L*physicalTransfer d z^ri+
          omittedRestoredErrorConstant d Bcap C1 A*L*ε
        let aj:=omittedRestoredSpatialConstant d Bcap A*L*physicalTransfer d z^rj+
          omittedRestoredErrorConstant d Bcap C1 A*L*ε
        ‖((new.restrict S).delete Bi).extensionGreen q z i j-
          (g.omittedCommonModel T labels samples selector S).extensionGreen q z (e i) (e j)‖≤
          omittedNormalizationConstant d Bcap C1*ε+(Fintype.card J:ℝ)*(Bcap+2+(KM+KA))*ai*aj := by
  let A:=omittedCompletionObservationLogCap d β
  have hAobs : 0≤sourceObservationLogCap d β := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hApart : 0≤sourcePartialObservationLogCap d β := by unfold sourcePartialObservationLogCap;positivity
  have hA : 0≤A := by dsimp only [A,omittedCompletionObservationLogCap];positivity
  filter_upwards [eventually_source_local_common_incidence_rows a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_omitted_kept_leaf_decay a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_omitted_kept_control a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_formal_diagonal_bounds a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds a b d c β Bcap C1 ha hb hd hc hβ hβc hC1]
    with N hrows hleaf hnorm hformal hnum
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let S:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
  let W:=s.selectedFirstSet selector
  let Bi:=s.partialFirstRemovedSet selector S
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  let e:=restrictionDeletionGraphIso new.graph S W Bi (fun _=>Iff.rfl)
  letI:DecidableEq (s.OmittedCore selector S):=fun a b=>Classical.propDecidable (a=b)
  have hS:=s.switched_pairBall_subset_old_augmentation selector r x y
  have hr:=hrows g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS
  have hl:=hleaf g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS
  have hn:=hnorm g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS
  have hf:=hformal z q hz hzB hfloor hprior
  have num:=hnum z hz hfloor
  have hB:0≤Bcap:=(norm_nonneg z).trans hzB
  have hCe:0≤finiteExtraReferenceConstant d:=by linarith [finiteExtraReferenceConstant_ge_one d hd]
  have hKM:0≤leafDeletedMateRowCap d Bcap:=by unfold leafDeletedMateRowCap;positivity
  have hKA:0≤leafDeletedSeparatedRowCap d Bcap:=by unfold leafDeletedSeparatedRowCap;positivity
  intro i j ri rj hri hrj hi hj
  have hc:=g.actual_omitted_completion_comparison hd T labels samples selector S q z Bcap C1 A
    (Real.log (N:ℝ)) (graphPaperError a d N (logarithmicRadius β d N) z)
    (leafDeletedMateRowCap d Bcap) (leafDeletedSeparatedRowCap d Bcap) hz hq hzB hf.2.2.1
    hA (by linarith [num.log_one]) num.error_nonnegative hKM hKA hr hl hn
    (e i) (e j) ri rj
    (fun l=>s.shifted_omittedKept_root_distance selector r ri hri x y (e i) hi l)
    (fun l=>s.shifted_omittedKept_root_distance_right selector r rj hrj x y (e j) hj l)
  have he:=congrArg (fun P=>P i j) (g.canonical_omitted_restored_Green T labels samples selector S q z)
  change (g.omittedKeptRestoredModel T labels samples selector S).extensionGreen q z (e i) (e j)=
    ((new.restrict S).delete Bi).extensionGreen q z i j at he
  rw [he] at hc
  exact hc

end RegularGraph
end LocalLaw
