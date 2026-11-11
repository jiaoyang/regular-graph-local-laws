import LocalLaw.SourceFullExteriorComparisonFamily
import LocalLaw.SourceFullRegionModelComparison
import LocalLaw.SourceFullRegionOuterComparison

/-! # Proved structured exterior comparison family

The actual common and local upper models are compared by deleting the far
samples on each side and restoring the same captured inner star. Every
analytic, geometric, inverse and numerical input comes from source factories.
-/
open Filter
noncomputable section
set_option maxHeartbeats 3500000
namespace LocalLaw
local instance sourceFullExteriorProofDecidable (p:Prop):Decidable p:=Classical.propDecidable p
local instance (priority := 2000) sourceFullExteriorProofRangeDecidable {L W:Type}(a:L↪W):
    DecidablePred (fun v:W=>v∈Set.range a):=fun _=>Classical.propDecidable _

theorem source_full_exterior_comparison_family (a b d:ℕ)(c β Bcap C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hC1:1≤C1):
    SourceFullExteriorComparisonFamily a b d c β Bcap C1:=by
  let Main:=sourceFullRegionModelMain d β Bcap C1+2*sourceFullRegionOuterMain d β Bcap C1
  let Tail:=sourceFullRegionModelTail d β Bcap C1+2*sourceFullRegionOuterTail d β Bcap C1
  let K:=|Main|+|Tail|+1
  refine ⟨K,by dsimp only[K];positivity,?_⟩
  filter_upwards [RegularGraph.eventually_source_full_region_model_comparison a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    RegularGraph.eventually_source_full_region_outer_comparison a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_resampling_radius_margin a d 2 8 β hd hβ,
    eventually_log_ge_nat 1,eventually_ge_atTop 1] with N hstar houter hmargin hroom hlog hN
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let S0:=s.fullSliceOutside (s.fullTwoTargetVertices selector r x y)
  let S1:=s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)
  let e:=s.fullPairOutsideEmbedding selector r x y
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  let μ:=Nat.card (BoundaryOrientedEdge g.graph T)
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  have hr:4≤r:=by dsimp only[r,effectiveModelRadius,modelRadiusLoss];omega
  have hsep:2*r≤selector:=by dsimp only[r,selector];omega
  have hsub:S1⊆S0:=fun _ hv=>s.switched_full_pair_subset_old_augmentation selector r x y hv
  have hregion0:(s.selectedFirstSet selector⊆S0 ∧ ∀i:s.AdmissibleSampleIndex selector,s.admissibleBoundaryVertex selector i∈S0) ∨
      Nat.card (s.partialFirstRemovedSet selector S0)≤2:=Or.inl
        ⟨s.selectedFirstSet_subset_fullRegion selector r x y,s.admissibleBoundaryVertex_mem_fullRegion selector r x y⟩
  have hregion1:(s.selectedFirstSet selector⊆S1 ∧ ∀i:s.AdmissibleSampleIndex selector,s.admissibleBoundaryVertex selector i∈S1) ∨
      Nat.card (s.partialFirstRemovedSet selector S1)≤2:=Or.inr (s.partialFirstRemovedSet_new_full_pair_card selector r hsep x y)
  intro loss hloss u v hu hv
  have hloss':loss≤r-2:=by omega
  have hOu:u.val∉s.fullRegionOuterFirst selector r x y:=s.fullRegion_near_not_outer selector r loss x y hloss' u.val hu
  have hOv:v.val∉s.fullRegionOuterFirst selector r x y:=s.fullRegion_near_not_outer selector r loss x y hloss' v.val hv
  let O:=s.fullRegionOuterFirst selector r x y
  let I:=s.fullRegionStarCore selector r x y u.val v.val
  let J:=s.fullRegionInnerFirst selector r x y
  let layout:=s.fullRegionStarLayout selector r (by omega:1≤r) x y u.val v.val u.property v.property
  let W0:Set S0:={w|w.val∈O}
  let W1:Set S1:={w|w.val∈O}
  let M0:=(new.restrict S0).delete W0
  let M1:=(new.restrict S1).delete W1
  let aJ:=restrictedStarInner S0 O J layout.inner_left layout.inner_not_outer
  let bJ:=restrictedStarInner S1 O J layout.inner_right layout.inner_not_outer
  let eI:=restrictedStarCore S0 O I J layout.core_left layout.core_not_outer layout.inner_left layout.inner_not_outer layout.core_not_inner
  let fI:=restrictedStarCore S1 O I J layout.core_right layout.core_not_outer layout.inner_right layout.inner_not_outer layout.core_not_inner
  let E:=embeddedStarEmbedding aJ eI
  let F:=embeddedStarEmbedding bJ fI
  let cover:=s.fullRegionStarCore_targets selector r x y u.val v.val hOu hOv
  let tx:=starTargetIndex I J u.val cover.1
  let ty:=starTargetIndex I J v.val cover.2
  let u0:(W0ᶜ:Set S0):=⟨e u,hOu⟩
  let v0:(W0ᶜ:Set S0):=⟨e v,hOv⟩
  let u1:(W1ᶜ:Set S1):=⟨u,hOu⟩
  let v1:(W1ᶜ:Set S1):=⟨v,hOv⟩
  have hEu:E tx=u0:=Subtype.ext (Subtype.ext (restrictedStarTarget_value S0 O I J layout.core_left layout.core_not_outer
    layout.inner_left layout.inner_not_outer layout.core_not_inner u.val cover.1))
  have hEv:E ty=v0:=Subtype.ext (Subtype.ext (restrictedStarTarget_value S0 O I J layout.core_left layout.core_not_outer
    layout.inner_left layout.inner_not_outer layout.core_not_inner v.val cover.2))
  have hFu:F tx=u1:=Subtype.ext (Subtype.ext (restrictedStarTarget_value S1 O I J layout.core_right layout.core_not_outer
    layout.inner_right layout.inner_not_outer layout.core_not_inner u.val cover.1))
  have hFv:F ty=v1:=Subtype.ext (Subtype.ext (restrictedStarTarget_value S1 O I J layout.core_right layout.core_not_outer
    layout.inner_right layout.inner_not_outer layout.core_not_inner v.val cover.2))
  have hs:=hstar g o z q hz hzB hfloor hq hprior hballs labels samples x y (by omega:1≤r)
    u.val v.val u.property v.property hOu hOv loss hu hv
  change ‖M0.extensionGreen q z (E tx) (E ty)-M1.extensionGreen q z (F tx) (F ty)‖≤_ at hs
  rw[hEu,hEv,hFu,hFv] at hs
  have ho0:=houter g o z q hz hzB hfloor hq hprior hballs labels samples x y S0 Set.Subset.rfl hregion0
    loss hloss u0 v0 hu hv
  have ho1:=houter g o z q hz hzB hfloor hq hprior hballs labels samples x y S1 hsub hregion1
    loss hloss u1 v1 hu hv
  have ho1rev:‖M1.extensionGreen q z u1 v1-(new.restrict S1).extensionGreen q z u v‖≤
      sourceFullRegionOuterMain d β Bcap C1*L*ε+
        sourceFullRegionOuterTail d β Bcap C1*((μ:ℝ)+1)*L^4*physicalTransfer d z^(2*(r-loss)):=by
    rw[norm_sub_rev]
    exact ho1
  have ht1:=norm_sub_le_norm_sub_add_norm_sub
    ((new.restrict S0).extensionGreen q z (e u) (e v)) (M0.extensionGreen q z u0 v0)
    ((new.restrict S1).extensionGreen q z u v)
  have ht2:=norm_sub_le_norm_sub_add_norm_sub (M0.extensionGreen q z u0 v0) (M1.extensionGreen q z u1 v1)
    ((new.restrict S1).extensionGreen q z u v)
  have hraw:‖(new.restrict S0).extensionGreen q z (e u) (e v)-(new.restrict S1).extensionGreen q z u v‖≤
      Main*L*ε+Tail*((μ:ℝ)+1)*L^4*physicalTransfer d z^(2*(r-loss)):=
    (ht1.trans (add_le_add ho0 (ht2.trans (add_le_add hs ho1rev)))).trans_eq (by dsimp only[Main,Tail];ring)
  have hL:0≤L:=by dsimp only[L];linarith
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hMK:Main≤K:=by dsimp only[K];linarith[le_abs_self Main,abs_nonneg Tail]
  have hTK:Tail≤K:=by dsimp only[K];linarith[le_abs_self Tail,abs_nonneg Main]
  exact hraw.trans (add_le_add
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMK hL) hε)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hTK (by positivity:0≤(μ:ℝ)+1)) (pow_nonneg hL 4))
        (pow_nonneg (physicalTransfer_pos d hd z).le _)))

end LocalLaw
