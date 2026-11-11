import LocalLaw.PartitionedStarDeletionCanonical
import LocalLaw.RemainingPairMixedRadius
import LocalLaw.SourceDeletedCoreComparison
import LocalLaw.SourceOmittedRestoredEntryCap
import LocalLaw.SourceCommonLeafArbitraryCaps
import LocalLaw.FiniteStarTargets
import LocalLaw.OmittedLeafCardinality
import LocalLaw.SelectedLeafCardinality

/-! # Actual asymmetric core errors for the finite inner-star reduction

The nested deletion blocks are identified with the literal total sampled-B
deletion blocks. Mixed and zero remaining radii retain the correct captures.
All core caps and both leaf counts follow from the actual source factories.
-/

open Filter
noncomputable section
set_option maxHeartbeats 2500000
namespace LocalLaw
local instance sourceInnerCoreDecidable (p:Prop):Decidable p:=Classical.propDecidable p
local instance (priority := 2000) sourceInnerCoreRangeDecidable {L W:Type}(a:L↪W) :
    DecidablePred (fun v:W=>v∈Set.range a):=fun _=>Classical.propDecidable _

def sourceInnerStarCoreMain (d:ℕ)(β B C1:ℝ):ℝ:=
  |omittedCompletionErrorConstant d B C1 (omittedCompletionObservationLogCap d β)+
    leafCompletionMainCoefficient d B (leafCompletionObservationLogCap d β) C1|+1

def sourceInnerStarCoreTail (d:ℕ)(β B:ℝ):ℝ:=
  |omittedCompletionTailConstant d B (omittedCompletionObservationLogCap d β)|+
    |leafCompletionTailCoefficient d B|+1

def sourceInnerStarCoreCap (d:ℕ)(B C1:ℝ):ℝ:=
  |omittedRestoredEntryCap d B C1|+|leafDeletedCoreUniformCap d B|+1

def sourceInnerStarLeafCount (d:ℕ):ℝ:=(2*(d:ℝ)+1)*(d:ℝ)*((d:ℝ)+1)

namespace RegularGraph

theorem eventually_source_inner_star_core_bounds (a b d:ℕ)(c β Bcap C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hC1:1≤C1) :
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z q:ℂ),
      0<z.im→‖z‖≤Bcap→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z)→
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d)→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      ∀hr:1≤r,
      let S₀:=s.twoTargetEndpointVertices selector r x y
      let S₁:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
      let O:=s.outerFirstSet selector r x y
      let I:=s.innerStarDeletedCore selector r x y
      let J:=s.innerFirstSet selector r x y
      let h:=s.innerStarLayout selector r hr x y
      let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
      let M₀:=(new.restrict S₀).delete {v:S₀|v.val∈O}
      let M₁:=(new.restrict S₁).delete {v:S₁|v.val∈O}
      let aJ:=restrictedStarInner S₀ O J h.inner_left h.inner_not_outer
      let bJ:=restrictedStarInner S₁ O J h.inner_right h.inner_not_outer
      let eI:=restrictedStarCore S₀ O I J h.core_left h.core_not_outer h.inner_left h.inner_not_outer h.core_not_inner
      let fI:=restrictedStarCore S₁ O I J h.core_right h.core_not_outer h.inner_right h.inner_not_outer h.core_not_inner
      let R:=((M₀.delete (Set.range aJ)).extensionGreen q z).submatrix eI eI
      let P:=((M₁.delete (Set.range bJ)).extensionGreen q z).submatrix fI fI
      let oldAug:=(g.deficient.delete T).restrict S₀
      let Baug:=s.partialFirstRemovedSet selector S₀
      let n:=Nat.card (s.OmittedOrdinaryLeaves selector S₁⊕s.OmittedExtraLeaves selector S₁)+
        Nat.card (DeletedLeafIndex oldAug.graph Baug)
      let ri:=fun i:I=>remainingPairRadius (outsideGraph (s.fullResample selector).graph T) r x y i.val
      let L:=Real.log (N:ℝ)
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      (n:ℝ)≤sourceInnerStarLeafCount d*L^(2*a) ∧
      (∀i j:I,‖(R-P) i j‖≤sourceInnerStarCoreMain d β Bcap C1*L*ε+
        sourceInnerStarCoreTail d β Bcap*((n:ℝ)+1)*L^2*physicalTransfer d z^(ri i+ri j)) ∧
      (∀i j:I,‖(R-P) i j‖≤sourceInnerStarCoreCap d Bcap C1) := by
  filter_upwards [eventually_source_deleted_core_comparison a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_omitted_restored_entry_cap a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_common_leaf_uniform_caps_arbitrary a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_selected_counts a d ha hd,eventually_log_ge_nat 1,eventually_ge_atTop 1]
    with N hcompare hlocal hglobal hcounts hlog hN
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  intro hr
  let S₀:=s.twoTargetEndpointVertices selector r x y
  let S₁:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
  let O:=s.outerFirstSet selector r x y
  let I:=s.innerStarDeletedCore selector r x y
  let J:=s.innerFirstSet selector r x y
  let layout:=s.innerStarLayout selector r hr x y
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  let M₀:=(new.restrict S₀).delete {v:S₀|v.val∈O}
  let M₁:=(new.restrict S₁).delete {v:S₁|v.val∈O}
  let aJ:=restrictedStarInner S₀ O J layout.inner_left layout.inner_not_outer
  let bJ:=restrictedStarInner S₁ O J layout.inner_right layout.inner_not_outer
  let eI:=restrictedStarCore S₀ O I J layout.core_left layout.core_not_outer layout.inner_left layout.inner_not_outer layout.core_not_inner
  let fI:=restrictedStarCore S₁ O I J layout.core_right layout.core_not_outer layout.inner_right layout.inner_not_outer layout.core_not_inner
  let oldAug:=(g.deficient.delete T).restrict S₀
  let Baug:=s.partialFirstRemovedSet selector S₀
  let Bi:=s.partialFirstRemovedSet selector S₁
  let W:=s.selectedFirstSet selector
  let hpart:J∪O=W:=s.inner_outer_partition selector r x y
  let φ₀:=partitionedStarDeletionEquiv S₀ O J W layout.inner_left layout.inner_not_outer hpart
  let φ₁:=partitionedStarDeletionEquiv S₁ O J W layout.inner_right layout.inner_not_outer hpart
  let u₀:=fun i:I=>φ₀ (eI i)
  let u₁:=fun i:I=>φ₁ (fI i)
  let ri:=fun i:I=>remainingPairRadius (outsideGraph (s.fullResample selector).graph T) r x y i.val
  let Keep:=s.OmittedOrdinaryLeaves selector S₁⊕s.OmittedExtraLeaves selector S₁
  let n:=Nat.card Keep+Nat.card (DeletedLeafIndex oldAug.graph Baug)
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let Main:=leafCompletionMainCoefficient d Bcap (leafCompletionObservationLogCap d β) C1
  let Tail:=leafCompletionTailCoefficient d Bcap
  let A:=omittedCompletionObservationLogCap d β
  have hSA:S₁⊆S₀:=s.switched_pairBall_subset_old_augmentation selector r x y
  let lift:=s.commonRegionEmbedding selector S₀ S₁ hSA
  have hlift (i:I):lift (u₁ i)=u₀ i:=rfl
  letI:DecidableEq (Baugᶜ:Set S₀):=fun a b=>Classical.propDecidable (a=b)
  have hR:=new.partitionedStar_core_extensionGreen_canonical S₀ O J W layout.inner_left layout.inner_not_outer hpart eI q z
  have hP:=new.partitionedStar_core_extensionGreen S₁ O J W layout.inner_right layout.inner_not_outer hpart fI q z
  have hc:=hcompare g o z q hz hzB hfloor hq hprior hballs labels samples x y
  have hl:=hlocal g o z q hz hzB hfloor hq hprior hballs labels samples x y S₁ hSA
  have hg:=hglobal g o z q hz hzB hfloor hq hprior hballs labels samples x y Set.univ
  have hnew:=g.restricted_selectedFirst_deletion_eq T labels samples selector S₀
    (s.selectedFirstSet_subset_twoTarget selector r x y)
  have hcountK:Nat.card Keep≤(d+1)*Nat.card (BoundaryOrientedEdge g.graph T):=by
    have hi:Nat.card Keep≤Nat.card (s.OmittedOldLeaves selector S₁⊕s.OmittedExtraLeaves selector S₁):=
      Nat.card_le_card_of_injective (s.omittedKeptEmbedding selector S₁) (s.omittedKeptEmbedding selector S₁).injective
    exact hi.trans (g.omittedAllLeaves_card_bound T labels samples selector S₁)
  have hcountD:Nat.card (DeletedLeafIndex oldAug.graph Baug)≤d*Nat.card (BoundaryOrientedEdge g.graph T):=
    g.partialFirst_deletedLeaf_card_bound T labels samples selector S₀
  have hn:n≤(2*d+1)*Nat.card (BoundaryOrientedEdge g.graph T):=by
    calc
      _≤(d+1)*Nat.card (BoundaryOrientedEdge g.graph T)+d*Nat.card (BoundaryOrientedEdge g.graph T):=
        Nat.add_le_add hcountK hcountD
      _=_:=by ring
  have hcount:(n:ℝ)≤sourceInnerStarLeafCount d*L^(2*a):=by
    have hmu:((Nat.card (BoundaryOrientedEdge g.graph T)):ℝ)≤(d:ℝ)*((d:ℝ)+1)*L^(2*a):=by
      have hbnd:=(hcounts g o z).2
      exact hbnd.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hlog (show 2*a-4≤2*a by omega)) (by positivity))
    have hh: (n:ℝ)≤(2*(d:ℝ)+1)*(Nat.card (BoundaryOrientedEdge g.graph T):ℝ):=by exact_mod_cast hn
    exact hh.trans ((mul_le_mul_of_nonneg_left hmu (by positivity)).trans_eq (by unfold sourceInnerStarLeafCount;ring))
  refine ⟨hcount,?_,?_⟩
  · intro i j
    rw[hR,hP]
    change ‖((new.restrict S₀).delete Baug).extensionGreen q z (u₀ i) (u₀ j)-
      ((new.restrict S₁).delete Bi).extensionGreen q z (u₁ i) (u₁ j)‖≤_
    rw[norm_sub_rev]
    have hh:=hc (u₁ i) (u₁ j) (ri i) (ri j)
      (remainingPairRadius_le _ _ _ _ _) (remainingPairRadius_le _ _ _ _ _)
      (remainingPairRadius_mixed _ _ _ _ _) (remainingPairRadius_mixed _ _ _ _ _)
    rw[hlift i,hlift j] at hh
    have hL:0≤L:=by linarith
    have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
    have hMain:omittedCompletionErrorConstant d Bcap C1 A+Main≤sourceInnerStarCoreMain d β Bcap C1:=by
      exact (le_abs_self _).trans (le_add_of_nonneg_right (by norm_num))
    have ht₁:omittedCompletionTailConstant d Bcap A≤sourceInnerStarCoreTail d β Bcap:=by
      dsimp only[sourceInnerStarCoreTail]
      linarith [le_abs_self (omittedCompletionTailConstant d Bcap A),abs_nonneg Tail]
    have ht₂:Tail≤sourceInnerStarCoreTail d β Bcap:=by
      dsimp only[sourceInnerStarCoreTail]
      linarith [le_abs_self Tail,abs_nonneg (omittedCompletionTailConstant d Bcap A)]
    have hV:0≤sourceInnerStarCoreTail d β Bcap:=by unfold sourceInnerStarCoreTail;positivity
    have hK:0≤(Nat.card Keep:ℝ):=Nat.cast_nonneg _
    have hD:0≤(Nat.card (DeletedLeafIndex oldAug.graph Baug):ℝ):=Nat.cast_nonneg _
    have hL2:1≤L^2:=one_le_pow₀ hlog
    have hs₁:(Nat.card Keep:ℝ)*omittedCompletionTailConstant d Bcap A*L^2≤
        (Nat.card Keep:ℝ)*sourceInnerStarCoreTail d β Bcap*L^2:=by gcongr
    have hs₂:Tail*((Nat.card (DeletedLeafIndex oldAug.graph Baug):ℝ)+1)≤
        sourceInnerStarCoreTail d β Bcap*((Nat.card (DeletedLeafIndex oldAug.graph Baug):ℝ)+1)*L^2:=by
      exact (mul_le_mul_of_nonneg_right ht₂ (by positivity)).trans
        (le_mul_of_one_le_right (by positivity) hL2)
    have hs:(Fintype.card Keep:ℝ)*omittedCompletionTailConstant d Bcap A*L^2+
        Tail*((Nat.card (DeletedLeafIndex oldAug.graph Baug):ℝ)+1)≤
        sourceInnerStarCoreTail d β Bcap*((n:ℝ)+1)*L^2:=by
      simp only[←Nat.card_eq_fintype_card] at hs₁ ⊢
      dsimp only[n]
      push_cast
      nlinarith only[hs₁,hs₂]
    exact hh.trans (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMain hL) hε)
      (mul_le_mul_of_nonneg_right hs (pow_nonneg (physicalTransfer_pos d hd z).le _)))
  · intro i j
    rw[hR,hP]
    change ‖((new.restrict S₀).delete Baug).extensionGreen q z (u₀ i) (u₀ j)-
      ((new.restrict S₁).delete Bi).extensionGreen q z (u₁ i) (u₁ j)‖≤_
    have hG:‖((new.restrict S₀).delete Baug).extensionGreen q z (u₀ i) (u₀ j)‖≤leafDeletedCoreUniformCap d Bcap:=by
      rw[hnew]
      exact hg.1 (u₀ i) (u₀ j)
    have hPcap:=hl (u₁ i) (u₁ j)
    exact (norm_sub_le _ _).trans ((add_le_add hG hPcap).trans (by
      unfold sourceInnerStarCoreCap
      linarith [le_abs_self (leafDeletedCoreUniformCap d Bcap),le_abs_self (omittedRestoredEntryCap d Bcap C1)]))

end RegularGraph
end LocalLaw
