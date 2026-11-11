import LocalLaw.FullRegionStarReduction
import LocalLaw.PartitionedStarDeletion
import LocalLaw.RemainingPairMixedRadius
import LocalLaw.SourceFullRegionCoreComparison

/-! # Native core bounds for actual full-region sampled-star restoration

The outer-then-inner deletion is flattened on both sides to literal total
selected-B deletion. The actual full-region comparison supplies the strong
asymmetric error, boundary count and fixed entry cap, including inside-T
original pair centers and zero remaining radii.
-/
open Filter
noncomputable section
set_option maxHeartbeats 2500000
namespace LocalLaw
local instance sourceFullStarCoreBoundsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
local instance (priority := 2000) sourceFullStarCoreRangeDecidable {L W:Type}(a:L↪W):
    DecidablePred (fun v:W=>v∈Set.range a):=fun _=>Classical.propDecidable _
namespace RegularGraph

theorem eventually_source_full_star_core_bounds (a b d:ℕ)(c β Bcap C1:ℝ)
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
      ∀(u v:(Tᶜ:Set (Fin N)))(hu:u∈S1)(hv:v∈S1),
      1≤r ∧ ∀hr:1≤r,
      let O:=s.fullRegionOuterFirst selector r x y
      let I:=s.fullRegionStarCore selector r x y u v
      let J:=s.fullRegionInnerFirst selector r x y
      let h:=s.fullRegionStarLayout selector r hr x y u v hu hv
      let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
      let M0:=(new.restrict S0).delete {v:S0|v.val∈O}
      let M1:=(new.restrict S1).delete {v:S1|v.val∈O}
      let aJ:=restrictedStarInner S0 O J h.inner_left h.inner_not_outer
      let bJ:=restrictedStarInner S1 O J h.inner_right h.inner_not_outer
      let eI:=restrictedStarCore S0 O I J h.core_left h.core_not_outer h.inner_left h.inner_not_outer h.core_not_inner
      let fI:=restrictedStarCore S1 O I J h.core_right h.core_not_outer h.inner_right h.inner_not_outer h.core_not_inner
      let R:=((M0.delete (Set.range aJ)).extensionGreen q z).submatrix eI eI
      let P:=((M1.delete (Set.range bJ)).extensionGreen q z).submatrix fI fI
      let ri:=fun i:I=>remainingPairRadius (s.fullResample selector).graph r x y i.val.val
      let μ:=Nat.card (BoundaryOrientedEdge g.graph T)
      let L:=Real.log (N:ℝ)
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      (μ:ℝ)≤(d:ℝ)*((d:ℝ)+1)*L^(2*a) ∧
      (∀i j:I,‖(R-P) i j‖≤sourceFullRegionCoreMain d β Bcap C1*L*ε+
        sourceFullRegionCoreTail d β Bcap*((μ:ℝ)+1)*L^2*physicalTransfer d z^(ri i+ri j)) ∧
      ∀i j:I,‖(R-P) i j‖≤sourceFullRegionCoreCap d Bcap C1:=by
  filter_upwards [eventually_source_full_region_core_comparison a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc]
    with N hcompare hmargins
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let S0:=s.fullSliceOutside (s.fullTwoTargetVertices selector r x y)
  let S1:=s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)
  intro u v hu hv
  refine ⟨hmargins.2.1,?_⟩
  intro hr
  let O:=s.fullRegionOuterFirst selector r x y
  let I:=s.fullRegionStarCore selector r x y u v
  let J:=s.fullRegionInnerFirst selector r x y
  let layout:=s.fullRegionStarLayout selector r hr x y u v hu hv
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  let M0:=(new.restrict S0).delete {v:S0|v.val∈O}
  let M1:=(new.restrict S1).delete {v:S1|v.val∈O}
  let aJ:=restrictedStarInner S0 O J layout.inner_left layout.inner_not_outer
  let bJ:=restrictedStarInner S1 O J layout.inner_right layout.inner_not_outer
  let eI:=restrictedStarCore S0 O I J layout.core_left layout.core_not_outer layout.inner_left layout.inner_not_outer layout.core_not_inner
  let fI:=restrictedStarCore S1 O I J layout.core_right layout.core_not_outer layout.inner_right layout.inner_not_outer layout.core_not_inner
  let B0:=s.partialFirstRemovedSet selector S0
  let B1:=s.partialFirstRemovedSet selector S1
  let W:=s.selectedFirstSet selector
  let hpart:J∪O=W:=s.fullRegion_inner_outer_partition selector r x y
  let φ0:=partitionedStarDeletionEquiv S0 O J W layout.inner_left layout.inner_not_outer hpart
  let φ1:=partitionedStarDeletionEquiv S1 O J W layout.inner_right layout.inner_not_outer hpart
  let u0:=fun i:I=>φ0 (eI i)
  let u1:=fun i:I=>φ1 (fI i)
  let ri:=fun i:I=>remainingPairRadius (s.fullResample selector).graph r x y i.val.val
  let hsub:S1⊆S0:=fun _ hv=>s.switched_full_pair_subset_old_augmentation selector r x y hv
  let lift:=s.commonRegionEmbedding selector S0 S1 hsub
  have hlift (i:I):lift (u1 i)=u0 i:=rfl
  have hR:=new.partitionedStar_core_extensionGreen S0 O J W layout.inner_left layout.inner_not_outer hpart eI q z
  have hP:=new.partitionedStar_core_extensionGreen S1 O J W layout.inner_right layout.inner_not_outer hpart fI q z
  have hc:=hcompare g o z q hz hzB hfloor hq hprior hballs labels samples x y
  refine ⟨hc.1,?_,?_⟩
  · intro i j
    rw[hR,hP]
    change ‖((new.restrict S0).delete B0).extensionGreen q z (u0 i) (u0 j)-
      ((new.restrict S1).delete B1).extensionGreen q z (u1 i) (u1 j)‖≤_
    have hh:=hc.2.1 (u1 i) (u1 j) (ri i) (ri j)
      (remainingPairRadius_le _ _ _ _ _) (remainingPairRadius_le _ _ _ _ _)
      (remainingPairRadius_mixed _ _ _ _ _) (remainingPairRadius_mixed _ _ _ _ _)
    rw[hlift i,hlift j] at hh
    exact hh
  · intro i j
    rw[hR,hP]
    change ‖((new.restrict S0).delete B0).extensionGreen q z (u0 i) (u0 j)-
      ((new.restrict S1).delete B1).extensionGreen q z (u1 i) (u1 j)‖≤_
    have hh:=hc.2.2 (u1 i) (u1 j)
    rw[hlift i,hlift j] at hh
    exact hh

end RegularGraph
end LocalLaw
