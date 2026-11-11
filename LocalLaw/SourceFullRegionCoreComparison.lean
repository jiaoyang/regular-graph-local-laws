import LocalLaw.SourceFullOmittedCompletionComparison
import LocalLaw.SourceCommonLeafArbitrary
import LocalLaw.CanonicalRestrictedCommonLocalModel
import LocalLaw.CommonRegionEmbedding
import LocalLaw.FullSelectedCommonCapture
import LocalLaw.SourceOmittedRestoredEntryCap
import LocalLaw.OmittedLeafCardinality
import LocalLaw.SharpSamplingCounts

/-! # Actual full-region comparison after all selected B vertices are deleted

Both actual regions are compared with restrictions of the same old common
model. Every omitted-B charge is handled by its genuine leaf completion.
The original full targets can lie in T. Only the spatial term pays the
boundary-label count; the ordinary error and entry cap are fixed.
-/
open Filter
noncomputable section
set_option maxHeartbeats 6500000
namespace LocalLaw
local instance sourceFullRegionCoreDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceFullRegionCoreMain (d:ℕ)(β B C1:ℝ):ℝ:=
  2*(|omittedCompletionErrorConstant d B C1 (omittedCompletionObservationLogCap d β)+
    leafCompletionMainCoefficient d B (leafCompletionObservationLogCap d β) C1|+1)

def sourceFullRegionCoreTail (d:ℕ)(β B:ℝ):ℝ:=
  2*((d:ℝ)+1)*(|omittedCompletionTailConstant d B (omittedCompletionObservationLogCap d β)|+
    |leafCompletionTailCoefficient d B|+1)

def sourceFullRegionCoreCap (d:ℕ)(B C1:ℝ):ℝ:=2*|omittedRestoredEntryCap d B C1|+1

namespace RegularGraph

theorem eventually_source_full_region_core_comparison (a b d:ℕ)(c β Bcap C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hC1:1≤C1):
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z q:ℂ),
      0<z.im→‖z‖≤Bcap→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z)→
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d)→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:Fin N),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      let S0:=s.fullSliceOutside (s.fullTwoTargetVertices selector r x y)
      let S1:=s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)
      let hsub:S1⊆S0:=fun _ hv=>s.switched_full_pair_subset_old_augmentation selector r x y hv
      let B0:=s.partialFirstRemovedSet selector S0
      let B1:=s.partialFirstRemovedSet selector S1
      let lift:=s.commonRegionEmbedding selector S0 S1 hsub
      let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
      let μ:=Nat.card (BoundaryOrientedEdge g.graph T)
      let L:=Real.log (N:ℝ)
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      (μ:ℝ)≤(d:ℝ)*((d:ℝ)+1)*L^(2*a) ∧
      (∀(i j:(B1ᶜ:Set S1))(ri rj:ℕ),ri≤r → rj≤r →
        (ri=0 ∨ (s.fullResample selector).graph.edist x i.val.val.val≤((r-ri:ℕ):ℕ∞) ∨
          (s.fullResample selector).graph.edist y i.val.val.val≤((r-ri:ℕ):ℕ∞))→
        (rj=0 ∨ (s.fullResample selector).graph.edist x j.val.val.val≤((r-rj:ℕ):ℕ∞) ∨
          (s.fullResample selector).graph.edist y j.val.val.val≤((r-rj:ℕ):ℕ∞))→
        ‖((new.restrict S0).delete B0).extensionGreen q z (lift i) (lift j)-
          ((new.restrict S1).delete B1).extensionGreen q z i j‖≤
        sourceFullRegionCoreMain d β Bcap C1*L*ε+
          sourceFullRegionCoreTail d β Bcap*((μ:ℝ)+1)*L^2*physicalTransfer d z^(ri+rj)) ∧
      ∀i j:(B1ᶜ:Set S1),
        ‖((new.restrict S0).delete B0).extensionGreen q z (lift i) (lift j)-
          ((new.restrict S1).delete B1).extensionGreen q z i j‖≤sourceFullRegionCoreCap d Bcap C1:=by
  filter_upwards [eventually_source_full_omitted_completion_comparison a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_common_leaf_localization_arbitrary a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_omitted_restored_entry_cap a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_inner_complement_nonempty a d (by omega) hd,
    eventually_actual_boundary_card_log_bound a d hd (by omega),
    eventually_log_ge_nat 1,eventually_ge_atTop 1]
    with N hcompletion hbaseline hcap hdummy hμ hlog hN
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let S0:=s.fullSliceOutside (s.fullTwoTargetVertices selector r x y)
  let S1:=s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)
  let hsub:S1⊆S0:=fun _ hv=>s.switched_full_pair_subset_old_augmentation selector r x y hv
  let B0:=s.partialFirstRemovedSet selector S0
  let B1:=s.partialFirstRemovedSet selector S1
  let lift:=s.commonRegionEmbedding selector S0 S1 hsub
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  let μ:=Nat.card (BoundaryOrientedEdge g.graph T)
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let A:=omittedCompletionObservationLogCap d β
  let Main:=leafCompletionMainCoefficient d Bcap (leafCompletionObservationLogCap d β) C1
  let Tail:=leafCompletionTailCoefficient d Bcap
  let CE:=omittedCompletionErrorConstant d Bcap C1 A
  let CT:=omittedCompletionTailConstant d Bcap A
  let w:(Tᶜ:Set (Fin N)):=Classical.choice (hdummy g o z)
  let px:=s.outsideReplacement w x
  let py:=s.outsideReplacement w y
  let Proxy:=s.twoTargetEndpointVertices selector r px py
  let h0:S0⊆Proxy:=s.fullTwoTarget_outside_subset_replacements selector r w x y
  let h1:S1⊆Proxy:=hsub.trans h0
  let M:=(g.deficient.delete T).restrict Proxy
  let BP:=s.partialFirstRemovedSet selector Proxy
  letI:DecidableEq (BPᶜ:Set Proxy):=fun a b=>Classical.propDecidable (a=b)
  let Global:=(M.delete BP).extensionGreen q z
  have hW:=s.selectedFirstSet_subset_twoTarget selector r px py
  have hL:0≤L:=by dsimp only[L];linarith
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have ht (n:ℕ):0≤physicalTransfer d z^n:=pow_nonneg (physicalTransfer_pos d hd z).le n
  have hRegion (S:Set (Tᶜ:Set (Fin N)))(hS:S⊆S0)(hcapture:S1⊆S)
      (u v:((s.partialFirstRemovedSet selector S)ᶜ:Set S))(ri rj:ℕ)
      (hri:ri≤r)(hrj:rj≤r)
      (hu:ri=0 ∨ (s.fullResample selector).graph.edist x u.val.val.val≤((r-ri:ℕ):ℕ∞) ∨
        (s.fullResample selector).graph.edist y u.val.val.val≤((r-ri:ℕ):ℕ∞))
      (hv:rj=0 ∨ (s.fullResample selector).graph.edist x v.val.val.val≤((r-rj:ℕ):ℕ∞) ∨
        (s.fullResample selector).graph.edist y v.val.val.val≤((r-rj:ℕ):ℕ∞))
      (huPair:u.val.val∈S1)(hvPair:v.val.val∈S1):
      let Bi:=s.partialFirstRemovedSet selector S
      let liftP:=s.commonRegionEmbedding selector Proxy S (hS.trans h0)
      ‖((new.restrict S).delete Bi).extensionGreen q z u v-Global (liftP u) (liftP v)‖≤
        (CE+Main)*L*ε+((Nat.card (s.OmittedOrdinaryLeaves selector S⊕s.OmittedExtraLeaves selector S):ℝ)*CT*L^2+
          Tail*((Nat.card (DeletedLeafIndex M.graph BP):ℝ)+1))*physicalTransfer d z^(ri+rj):=by
    dsimp only
    let Bi:=s.partialFirstRemovedSet selector S
    let hSP:=hS.trans h0
    let liftP:=s.commonRegionEmbedding selector Proxy S hSP
    let K:Set (BPᶜ:Set Proxy):={v|v.val.val∈S}
    let eN:=restrictionDeletionGraphIso new.graph S (s.selectedFirstSet selector) Bi (fun _=>Iff.rfl)
    letI:DecidableEq (s.OmittedCore selector S):=fun a b=>Classical.propDecidable (a=b)
    let uu:K:=⟨liftP u,u.val.property⟩
    let vv:K:=⟨liftP v,v.val.property⟩
    have hballU:graphBallVertices (M.delete BP).graph uu.val ri⊆K:=by
      intro t ht
      exact hcapture (s.selectedCommon_full_mixed_shifted_capture selector r ri hri Proxy x y uu.val huPair hu ht)
    have hballV:graphBallVertices (M.delete BP).graph vv.val rj⊆K:=by
      intro t ht
      exact hcapture (s.selectedCommon_full_mixed_shifted_capture selector r rj hrj Proxy x y vv.val hvPair hv ht)
    have hb:=hbaseline g o z q hz hzB hfloor hq hprior hballs labels samples px py K uu vv ri rj hballU hballV
    have hid:=congrArg (fun P=>P uu vv)
      (g.canonical_restricted_common_local_Green T labels samples selector Proxy S hW hSP q z)
    change (g.omittedCommonModel T labels samples selector S).extensionGreen q z (eN u) (eN v)=
      ((M.delete BP).restrict K).extensionGreen q z uu vv at hid
    rw[←hid] at hb
    have hb':‖(g.omittedCommonModel T labels samples selector S).extensionGreen q z (eN u) (eN v)-
        Global (liftP u) (liftP v)‖≤Main*L*ε+
          Tail*((Nat.card (DeletedLeafIndex M.graph BP):ℝ)+1)*physicalTransfer d z^(ri+rj):=by
      rw[norm_sub_rev]
      exact hb
    have hc:=hcompletion g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS hcapture
      u v ri rj hri hrj hu hv
    have hc':‖((new.restrict S).delete Bi).extensionGreen q z u v-
        (g.omittedCommonModel T labels samples selector S).extensionGreen q z (eN u) (eN v)‖≤
        CE*L*ε+(Nat.card (s.OmittedOrdinaryLeaves selector S⊕s.OmittedExtraLeaves selector S):ℝ)*
          CT*L^2*physicalTransfer d z^(ri+rj):=by
      simpa only[←Nat.card_eq_fintype_card] using hc
    have htriangle:=norm_sub_le_norm_sub_add_norm_sub
      (((new.restrict S).delete Bi).extensionGreen q z u v)
      ((g.omittedCommonModel T labels samples selector S).extensionGreen q z (eN u) (eN v))
      (Global (liftP u) (liftP v))
    exact (htriangle.trans (add_le_add hc' hb')).trans_eq (by ring)
  have hKept (S:Set (Tᶜ:Set (Fin N))):
      Nat.card (s.OmittedOrdinaryLeaves selector S⊕s.OmittedExtraLeaves selector S)≤(d+1)*μ:=
    (Nat.card_le_card_of_injective _ (s.omittedKeptEmbedding selector S).injective).trans
      (g.omittedAllLeaves_card_bound T labels samples selector S)
  have hFake:Nat.card (DeletedLeafIndex M.graph BP)≤d*μ:=
    g.partialFirst_deletedLeaf_card_bound T labels samples selector Proxy
  have hcaps0:=hcap g o z q hz hzB hfloor hq hprior hballs labels samples px py S0 h0
  have hcaps1:=hcap g o z q hz hzB hfloor hq hprior hballs labels samples px py S1 h1
  refine ⟨hμ g o z,?_,?_⟩
  · intro i j ri rj hri hrj hi hj
    have h0i:((lift i).val.val)∈S1:=i.val.property
    have h0j:((lift j).val.val)∈S1:=j.val.property
    have he0:=hRegion S0 Set.Subset.rfl hsub (lift i) (lift j) ri rj hri hrj hi hj h0i h0j
    have he1:=hRegion S1 hsub Set.Subset.rfl i j ri rj hri hrj hi hj i.val.property j.val.property
    let GP:=Global (s.commonRegionEmbedding selector Proxy S1 h1 i)
      (s.commonRegionEmbedding selector Proxy S1 h1 j)
    change ‖((new.restrict S0).delete B0).extensionGreen q z (lift i) (lift j)-GP‖≤_ at he0
    change ‖((new.restrict S1).delete B1).extensionGreen q z i j-GP‖≤_ at he1
    have htri:=norm_sub_le_norm_sub_add_norm_sub
      (((new.restrict S0).delete B0).extensionGreen q z (lift i) (lift j)) GP
      (((new.restrict S1).delete B1).extensionGreen q z i j)
    rw[norm_sub_rev GP] at htri
    have hh:=htri.trans (add_le_add he0 he1)
    have hm:2*(CE+Main)≤sourceFullRegionCoreMain d β Bcap C1:=by
      dsimp only[sourceFullRegionCoreMain,CE,Main,A]
      linarith[le_abs_self (omittedCompletionErrorConstant d Bcap C1 (omittedCompletionObservationLogCap d β)+
        leafCompletionMainCoefficient d Bcap (leafCompletionObservationLogCap d β) C1)]
    have hct:CT≤|CT|:=le_abs_self CT
    have htail:Tail≤|Tail|:=le_abs_self Tail
    have hK0:(Nat.card (s.OmittedOrdinaryLeaves selector S0⊕s.OmittedExtraLeaves selector S0):ℝ)≤((d:ℝ)+1)*(μ:ℝ):=by exact_mod_cast hKept S0
    have hK1:(Nat.card (s.OmittedOrdinaryLeaves selector S1⊕s.OmittedExtraLeaves selector S1):ℝ)≤((d:ℝ)+1)*(μ:ℝ):=by exact_mod_cast hKept S1
    have hNF:(Nat.card (DeletedLeafIndex M.graph BP):ℝ)≤(d:ℝ)*(μ:ℝ):=by exact_mod_cast hFake
    have hmu:0≤(μ:ℝ):=Nat.cast_nonneg _
    have hd0:0≤(d:ℝ):=Nat.cast_nonneg _
    have hL2:1≤L^2:=one_le_pow₀ hlog
    have hc0:(Nat.card (s.OmittedOrdinaryLeaves selector S0⊕s.OmittedExtraLeaves selector S0):ℝ)*CT*L^2≤
        (((d:ℝ)+1)*(μ:ℝ))*|CT| *L^2:=by
      exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hct (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hK0 (abs_nonneg CT))) (sq_nonneg L)
    have hc1:(Nat.card (s.OmittedOrdinaryLeaves selector S1⊕s.OmittedExtraLeaves selector S1):ℝ)*CT*L^2≤
        (((d:ℝ)+1)*(μ:ℝ))*|CT| *L^2:=by
      exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hct (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hK1 (abs_nonneg CT))) (sq_nonneg L)
    have hf:Tail*((Nat.card (DeletedLeafIndex M.graph BP):ℝ)+1)≤
        |Tail| *((d:ℝ)*(μ:ℝ)+1)*L^2:=by
      exact ((mul_le_mul_of_nonneg_right htail (by positivity)).trans
        (mul_le_mul_of_nonneg_left (add_le_add_right hNF 1) (abs_nonneg Tail))).trans
          (le_mul_of_one_le_right (by positivity) hL2)
    have htailTotal:
        ((Nat.card (s.OmittedOrdinaryLeaves selector S0⊕s.OmittedExtraLeaves selector S0):ℝ)*CT*L^2+
          Tail*((Nat.card (DeletedLeafIndex M.graph BP):ℝ)+1))+
        ((Nat.card (s.OmittedOrdinaryLeaves selector S1⊕s.OmittedExtraLeaves selector S1):ℝ)*CT*L^2+
          Tail*((Nat.card (DeletedLeafIndex M.graph BP):ℝ)+1))≤
        sourceFullRegionCoreTail d β Bcap*((μ:ℝ)+1)*L^2:=by
      have ht0:((d:ℝ)+1)*(μ:ℝ)≤((d:ℝ)+1)*((μ:ℝ)+1):=by nlinarith
      have ht1:(d:ℝ)*(μ:ℝ)+1≤((d:ℝ)+1)*((μ:ℝ)+1):=by nlinarith
      have hs0:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht0 (abs_nonneg CT)) (sq_nonneg L)
      have hs1:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht1 (abs_nonneg Tail)) (sq_nonneg L)
      have hextra:0≤2*((d:ℝ)+1)*((μ:ℝ)+1)*L^2:=by positivity
      change _≤2*((d:ℝ)+1)*(|CT|+|Tail|+1)*((μ:ℝ)+1)*L^2
      nlinarith only[hc0,hc1,hf,hs0,hs1,hextra]
    have hordinary:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm hL) hε
    have hspatial:=mul_le_mul_of_nonneg_right htailTotal (ht (ri+rj))
    exact hh.trans (by nlinarith only[hordinary,hspatial])
  · intro i j
    exact (norm_sub_le _ _).trans ((add_le_add (hcaps0 (lift i) (lift j)) (hcaps1 i j)).trans (by
      unfold sourceFullRegionCoreCap
      linarith[le_abs_self (omittedRestoredEntryCap d Bcap C1)]))

end RegularGraph
end LocalLaw
