import LocalLaw.SourceSelectedFarColumns
import LocalLaw.OuterFirstRegionGeometry
import LocalLaw.SourceFarDeletionSquare
import LocalLaw.SourcePartialFirstPrincipalCaps
import LocalLaw.PartialFirstRemovedRows
import LocalLaw.DeletionRowsInstanceAdapter

/-! # Removing the actual distant sampled vertices at nominal prime cost -/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
namespace LocalLaw
local instance sourceOuterFirstDeletionDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_outer_first_deletion (a b d:ℕ)(c β Bcap C1:ℝ)
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
      let A:=s.twoTargetEndpointVertices selector r x y
      let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict A
      let W:=s.outerFirstRegion selector r x y A
      ∀(u v:(Wᶜ:Set A)),u.val.val=x→v.val.val=y→
      ‖M.extensionGreen q z u.val v.val-(M.delete W).extensionGreen q z u v‖≤
        g.sourcePrime a (logarithmicRadius β d N) z := by
  let Count:ℝ:=(d:ℝ)*((d:ℝ)+1)
  let C:=4*sourcePartialFirstInverseCap d Bcap
  let Acoef:=|sourceSelectedFarLeading d β Bcap C1|+1
  let Dcoef:=|sourceSelectedFarError d β Bcap C1|+1
  have hCount:0≤Count:=by dsimp only [Count];positivity
  have hC:0≤C:=by
    have hh:=finiteExtraReferenceConstant_ge_one d hd
    dsimp only [C,sourcePartialFirstInverseCap]
    positivity
  have hA:0≤Acoef:=by dsimp only [Acoef];positivity
  have hD:0≤Dcoef:=by dsimp only [Dcoef];positivity
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_source_selected_far_columns a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_partial_first_principal_caps a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_far_deletion_square a b d β Bcap Count C Acoef Dcoef ha hb hd hβ hCount hC hA hD,
    eventually_resampling_radius_margin a d 2 6 β hd hβ,
    eventually_log_ge_nat 1,eventually_ge_atTop 1,hdepth] with N hfar hinv hrate hroom hlog hN hdepthN
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let A:=s.twoTargetEndpointVertices selector r x y
  let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict A
  let W:=s.outerFirstRegion selector r x y A
  let xl:A:=twoBallLeft (outsideGraph g.graph T) (s.endpointModelVertices selector r) x y r
  let yl:A:=twoBallRight (outsideGraph g.graph T) (s.endpointModelVertices selector r) x y r
  let hp:=s.outerFirstRegion_targets_not_mem selector r x y A xl.property yl.property
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let t:=physicalTransfer d z^(r-2)
  let F:=Acoef*L*t+Dcoef*L*ε
  have hL:0≤L:=by dsimp only [L];linarith
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have ht:0≤t:=pow_nonneg (physicalTransfer_pos d hd z).le _
  have hF:0≤F:=by dsimp only [F];positivity
  have hf:=hfar g o z q hz hzB hfloor hq hprior hballs labels samples x y
  have hindexed:=hinv g o z q hz hzB hfloor hq hprior hballs labels samples x y A (Set.Subset.refl _)
  have hwcaps:=s.removed_first_inverse_caps_of_indexed selector A (M.extensionGreen q z) C hindexed W
    (s.outerFirstRegion_subset_removed selector r x y A)
  have hbound (u:A)(v:W)(hgeo:(((r-2)+1:ℕ):ℕ∞)≤M.graph.edist u v.val) :
      ‖M.extensionGreen q z u v.val‖≤F := by
    let bv:s.partialFirstRemovedSet selector A:=⟨v.val,
      s.outerFirstRegion_subset_removed selector r x y A v.property⟩
    have hh:=hf u bv (r-2) hgeo
    have hAc:sourceSelectedFarLeading d β Bcap C1≤Acoef:=by
      dsimp only [Acoef];linarith [le_abs_self (sourceSelectedFarLeading d β Bcap C1)]
    have hDc:sourceSelectedFarError d β Bcap C1≤Dcoef:=by
      dsimp only [Dcoef];linarith [le_abs_self (sourceSelectedFarError d β Bcap C1)]
    exact hh.trans (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAc hL) ht)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDc hL) hε))
  have hgeometry (v:W):
      (((r-2)+1:ℕ):ℕ∞)≤M.graph.edist xl v.val ∧
      (((r-2)+1:ℕ):ℕ∞)≤M.graph.edist yl v.val :=
    s.outerFirstRegion_far selector r x y A xl.property yl.property v
  have hx:∀v:W,‖M.extensionGreen q z xl v.val‖≤F:=fun v=>hbound xl v (hgeometry v).1
  have hy:∀v:W,‖M.extensionGreen q z v.val yl‖≤F:=by
    intro v
    rw [M.extensionGreen_isSymm q z |>.apply yl v.val]
    exact hbound yl v (hgeometry v).2
  have hdelete:=M.far_deleted_target_difference_any_rows hd W q z hz hq C F F hC hF hF _ _ hwcaps.2.1
    ⟨xl,hp.1⟩ ⟨yl,hp.2⟩ hx hy
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hWcard:Nat.card W≤Nat.card (BoundaryOrientedEdge g.graph T):=by
    have hs:=s.outerFirstRegion_card selector r x y A
    have hi:Nat.card (s.AdmissibleSampleIndex selector)≤Nat.card ι:=by
      simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_le _
    exact hs.trans (hi.trans_eq (Nat.card_congr labels))
  have hcount:(Fintype.card W:ℝ)≤Count*L^(2*a):=by
    have hh:=(Nat.cast_le (α:=ℝ).mpr hWcard).trans (g.boundary_card_log_bound o a ell hd hlog hell)
    simpa only [Nat.card_eq_fintype_card] using hh
  have hr:2≤r:=by dsimp only [r,effectiveModelRadius,modelRadiusLoss];omega
  have hroom':modelRadiusLoss a d N≤logarithmicRadius β d N:=by
    dsimp only [modelRadiusLoss];omega
  have hbudget:=hrate z hz hzB hfloor hroom' hr (Fintype.card W) (Nat.cast_nonneg _) hcount
  have heq:(Fintype.card W:ℝ)*C*F*F=(Fintype.card W:ℝ)*C*F^2:=by ring
  have hout:‖M.extensionGreen q z xl yl-(M.delete W).extensionGreen q z ⟨xl,hp.1⟩ ⟨yl,hp.2⟩‖≤
      g.sourcePrime a (logarithmicRadius β d N) z := (hdelete.trans_eq heq).trans hbudget
  intro u v hu hv
  have hu':u=⟨xl,hp.1⟩:=Subtype.ext (Subtype.ext hu)
  have hv':v=⟨yl,hp.2⟩:=Subtype.ext (Subtype.ext hv)
  simpa only [hu',hv'] using hout

end RegularGraph
end LocalLaw
