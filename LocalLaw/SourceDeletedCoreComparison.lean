import LocalLaw.SourceOmittedCompletionComparisonMixed
import LocalLaw.SourceCommonLeafArbitrary
import LocalLaw.CanonicalRestrictedCommonLocalModel
import LocalLaw.CommonRegionEmbedding
import LocalLaw.SelectedCommonMixedCapture

/-! # Actual asymmetric comparison of the two switched deleted reference models

Both literal NEW models are compared after the selected B vertices are
removed. The common baseline is localized using arbitrary retained sets;
the local omitted-neighbor charge is restored by the proved completion.
Original pair centers may be selected B and secondary radii may be zero.
-/

open Filter
noncomputable section
set_option maxHeartbeats 5000000
namespace LocalLaw
local instance sourceDeletedCoreComparisonDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_deleted_core_comparison (a b d:ℕ)(c β Bcap C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hC1:1≤C1) :
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z q:ℂ),
      0<z.im → ‖z‖≤Bcap → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → 0≤q.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      let Aaug:=s.twoTargetEndpointVertices selector r x y
      let S:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
      let hSA:=s.switched_pairBall_subset_old_augmentation selector r x y
      let Baug:=s.partialFirstRemovedSet selector Aaug
      let Bi:=s.partialFirstRemovedSet selector S
      let lift:=s.commonRegionEmbedding selector Aaug S hSA
      let oldAug:=(g.deficient.delete T).restrict Aaug
      let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
      let J:=s.OmittedOrdinaryLeaves selector S⊕s.OmittedExtraLeaves selector S
      let A:=omittedCompletionObservationLogCap d β
      let L:=Real.log (N:ℝ)
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      let Main:=leafCompletionMainCoefficient d Bcap (leafCompletionObservationLogCap d β) C1
      let Tail:=leafCompletionTailCoefficient d Bcap
      letI:DecidableEq (Baugᶜ:Set Aaug):=fun a b=>Classical.propDecidable (a=b)
      ∀i j:(Biᶜ:Set S),∀ri rj:ℕ,ri≤r → rj≤r →
        (ri=0 ∨ (outsideGraph (s.fullResample selector).graph T).edist x i.val.val≤((r-ri:ℕ):ℕ∞) ∨
          (outsideGraph (s.fullResample selector).graph T).edist y i.val.val≤((r-ri:ℕ):ℕ∞)) →
        (rj=0 ∨ (outsideGraph (s.fullResample selector).graph T).edist x j.val.val≤((r-rj:ℕ):ℕ∞) ∨
          (outsideGraph (s.fullResample selector).graph T).edist y j.val.val≤((r-rj:ℕ):ℕ∞)) →
        ‖((new.restrict S).delete Bi).extensionGreen q z i j-
          ((new.restrict Aaug).delete Baug).extensionGreen q z (lift i) (lift j)‖≤
        (omittedCompletionErrorConstant d Bcap C1 A+Main)*L*ε+
          ((Fintype.card J:ℝ)*omittedCompletionTailConstant d Bcap A*L^2+
            Tail*((Nat.card (DeletedLeafIndex oldAug.graph Baug):ℝ)+1))*physicalTransfer d z^(ri+rj) := by
  filter_upwards [eventually_source_omitted_completion_comparison_mixed a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_common_leaf_localization_arbitrary a b d c β Bcap C1 ha hb hd hc hβ hβc hC1]
    with N hcompletion hbaseline
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let Aaug:=s.twoTargetEndpointVertices selector r x y
  let S:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
  let hSA:=s.switched_pairBall_subset_old_augmentation selector r x y
  let Baug:=s.partialFirstRemovedSet selector Aaug
  let Bi:=s.partialFirstRemovedSet selector S
  let lift:=s.commonRegionEmbedding selector Aaug S hSA
  let M:=(g.deficient.delete T).restrict Aaug
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  let K:Set (Baugᶜ:Set Aaug):={u | u.val.val∈S}
  let eC:=s.selectedCommonLocalEquiv selector Aaug S hSA
  let W:=s.selectedFirstSet selector
  let eN:=restrictionDeletionGraphIso new.graph S W Bi (fun _=>Iff.rfl)
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let Main:=leafCompletionMainCoefficient d Bcap (leafCompletionObservationLogCap d β) C1
  let Tail:=leafCompletionTailCoefficient d Bcap
  letI:DecidableEq (Baugᶜ:Set Aaug):=fun a b=>Classical.propDecidable (a=b)
  letI:DecidableEq (s.OmittedCore selector S):=fun a b=>Classical.propDecidable (a=b)
  have hW:=s.selectedFirstSet_subset_twoTarget selector r x y
  have hNewEq:=g.restricted_selectedFirst_deletion_eq T labels samples selector Aaug hW
  change ((new.restrict Aaug).delete Baug)=M.delete Baug at hNewEq
  rw [hNewEq]
  intro i j ri rj hri hrj hi hj
  let ii:K:=⟨lift i,i.val.property⟩
  let jj:K:=⟨lift j,j.val.property⟩
  have hcapI:graphBallVertices (M.delete Baug).graph ii.val ri⊆K:=
    s.selectedCommon_mixed_shifted_capture selector r ri hri Aaug x y ii.val ii.property hi
  have hcapJ:graphBallVertices (M.delete Baug).graph jj.val rj⊆K:=
    s.selectedCommon_mixed_shifted_capture selector r rj hrj Aaug x y jj.val jj.property hj
  have hb:=hbaseline g o z q hz hzB hfloor hq hprior hballs labels samples x y K ii jj ri rj hcapI hcapJ
  have hlocal:=congrArg (fun P=>P ii jj)
    (g.canonical_restricted_common_local_Green T labels samples selector Aaug S hW hSA q z)
  change (g.omittedCommonModel T labels samples selector S).extensionGreen q z (eN i) (eN j)=
    ((M.delete Baug).restrict K).extensionGreen q z ii jj at hlocal
  rw [←hlocal] at hb
  have hbsym : ‖(g.omittedCommonModel T labels samples selector S).extensionGreen q z (eN i) (eN j)-
      (M.delete Baug).extensionGreen q z (lift i) (lift j)‖≤
      Main*L*ε+Tail*((Nat.card (DeletedLeafIndex M.graph Baug):ℝ)+1)*physicalTransfer d z^(ri+rj) := by
    rw [norm_sub_rev]
    exact hb
  have hc:=hcompletion g o z q hz hzB hfloor hq hprior hballs labels samples x y i j ri rj hri hrj hi hj
  have ht:=norm_sub_le_norm_sub_add_norm_sub
    (((new.restrict S).delete Bi).extensionGreen q z i j)
    ((g.omittedCommonModel T labels samples selector S).extensionGreen q z (eN i) (eN j))
    ((M.delete Baug).extensionGreen q z (lift i) (lift j))
  apply (ht.trans (add_le_add hc hbsym)).trans_eq
  ring

end RegularGraph
end LocalLaw
