import LocalLaw.SourceFullAugmentedRows
import LocalLaw.FullAugmentedCapture
import LocalLaw.FullCommonLogParameters
import LocalLaw.RestrictedSurgeryRowStability

/-! Full physical Green comparison with the actual common two-target model.
The common NEW model is controlled by its proved rows, not a reference class. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceFullCommonSurgeryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 4000000
namespace RegularGraph

theorem eventually_source_full_common_surgery (a b d : ℕ) (c β B : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) :
    ∀ᶠ N : ℕ in Filter.atTop,∀(g : RegularGraph N d)(o : Fin N)(z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z →
      ∀{ι : Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : Fin N),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      let h:=g.labelledResampledGraph T labels samples selector
      let S:=s.fullTwoTargetVertices selector r x y
      let xl:=twoBallLeft g.graph (filledExteriorVertices T (s.endpointModelVertices selector r)) x y r
      let yl:=twoBallRight g.graph (filledExteriorVertices T (s.endpointModelVertices selector r)) x y r
      ‖h.G z x y-(h.deficient.restrict S).extensionGreen (g.Q z) z xl yl‖≤1/Real.log (N:ℝ) := by
  let A:=fullRestrictionLogCap d β
  let U:=fullEndpointCountConstant d+2
  let M:=sourceFullAugmentedRowConstant d β
  let w:=endpointSurgeryCouplingCap d
  let H:=max 1 (max (4*U*(1+M*w)*w) (4*(1+M*w)^2))
  have hAobs:sourceObservationLogCap d β≤A:=(fullRestrictionLogCap_properties d β).2.1
  have hU:0≤U:=by dsimp only [U,fullEndpointCountConstant]; positivity
  have hM:0≤M:=sourceFullAugmentedRowConstant_nonnegative d β hd
  have hw:0≤w:=by dsimp only [w,endpointSurgeryCouplingCap]; positivity
  have hH:1≤H:=le_max_left _ _
  filter_upwards [eventually_source_full_augmented_rows a b d c β B 1 ha hb hd hc hβ hβc le_rfl,
    eventually_source_fullTwoTarget_geometry a b d c β B ha hb hd hc hβ hβc,
    eventually_sourceObservationBounds_of_cap a b d c β B 1 A ha hb hd hc hβ hβc le_rfl hAobs,
    eventually_actual_fullPartialIndex_count a d ha hd,
    eventually_paperError_sharp_log_small a b d β H ha hb hd hβ hH,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc]
    with N hrows hgeo hnum hcount hsharp hmargin
  intro g o z hz hzB hfloor badCount hsource ι _ labels samples x y
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let h:=g.labelledResampledGraph T labels samples selector
  let S:=s.fullTwoTargetVertices selector r x y
  let xl:S:=twoBallLeft g.graph (filledExteriorVertices T (s.endpointModelVertices selector r)) x y r
  let yl:S:=twoBallRight g.graph (filledExteriorVertices T (s.endpointModelVertices selector r)) x y r
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  have hs:1≤selector:=by dsimp only [selector]; omega
  let e0:=s.fullPartialEmbedding selector S hs
  let I:=twoTargetIndexSet e0 xl yl
  let e:I↪S:=⟨Subtype.val,Subtype.val_injective⟩
  have num:=hnum z hz hfloor
  have hL0:0≤L:=by linarith [num.log_one]
  have hprior:‖g.Q z-semicircleRoot z‖≤1*scalarScale (spectralScale z) ε:=by
    simpa only [one_mul] using hsource.2.1
  have geo:=hgeo g o z hz hfloor hsource.1.1 labels samples x y
  have row:=hrows g o z (g.Q z) hz hzB hfloor (g.Q_im_nonnegative z hz) hprior hsource.1.1 labels samples x y hs S Set.Subset.rfl xl yl
  let C:=M*L^(2*a-2)
  have hC:0≤C:=by dsimp only [C]; positivity
  have hcol:∀j:I,∑i:I,‖(h.deficient.restrict S).extensionGreen (g.Q z) z (e i) (e j)‖≤C:=by
    intro j
    have heq:(∑i:I,‖(h.deficient.restrict S).extensionGreen (g.Q z) z (e i) (e j)‖)=
        ∑i:I,‖(h.deficient.restrict S).extensionGreen (g.Q z) z (e j) (e i)‖:=
      Finset.sum_congr rfl (fun i _=>congrArg norm (((h.deficient.restrict S).extensionGreen_isSymm (g.Q z) z).apply (e i) (e j)).symm)
    rw [heq]
    exact row j
  have hcard:(Fintype.card I:ℝ)≤U*L^(2*a-4):=by
    have hc:Nat.card I≤Fintype.card (s.FullEndpointIndex selector S)+2:=two_target_index_card e0 xl yl
    rw [Nat.card_eq_fintype_card] at hc
    have hn:(Fintype.card I:ℝ)≤(Fintype.card (s.FullEndpointIndex selector S):ℝ)+2:=by exact_mod_cast hc
    have hc0:=hcount g o z labels samples selector hs S
    rw [Nat.card_eq_fintype_card] at hc0
    have hp:1≤L^(2*a-4):=one_le_pow₀ num.log_one
    dsimp only [U]
    nlinarith only [hn,hc0,hp]
  have budgets:=full_common_log_budgets a L ε (Fintype.card I) C U M w H (by omega) num.log_one
    num.error_nonnegative hC hU hM hw hH hcard le_rfl
    ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
    (hsharp z hz hfloor)
  have hcapture:∀i:I,graphBallVertices g.deficient.graph (e i).val r⊆S:=by
    intro i
    apply geo.2.2.2.2
    rcases i.property with ⟨j,hj⟩ | hi
    · have hi':i.val=e0 j:=hj.symm
      change i.val.val∈s.fullEndpointRoots selector∪{x,y}
      rw [hi']
      exact Or.inl (s.fullPartialEmbedding_mem_roots selector S hs j)
    · rcases hi with hi | hi
      · exact Or.inr (Or.inl (congrArg Subtype.val hi))
      · exact Or.inr (Or.inr (congrArg Subtype.val hi))
  have hgraph:=s.fullTwoTarget_supported_on_augmented_index selector r hs x y
  have hpair:∀i j:I,‖g.deficient.G z (e i).val (e j).val-g.deficient.P r z (g.Q z) (e i).val (e j).val‖≤1*L^3*ε:=by
    intro i j
    rw [g.deficient_P]
    have hp:=hsource.2.2 (e i).val (e j).val
    change ‖g.G z (e i).val (e j).val-g.P r z (g.Q z) (e i).val (e j).val‖≤ε at hp
    exact hp.trans (by nlinarith only [one_le_pow₀ num.log_one (n:=3),num.error_nonnegative])
  have hfinal:=g.deficient.restricted_endpoint_surgery_stability_of_rows h.deficient hd S e r
    (fullTwoTargetDiameter d ell r) z (g.Q z) hz (g.Q_im_nonnegative z hz) B 1 ε L A hzB num
    (fun v=>by simpa using g.regular v) (fun v=>by simpa using h.regular v) hgraph
    geo.1.base.to_componentFinite geo.1.diameter
    (geo.1.diameter_log.trans (mul_le_mul_of_nonneg_right
      (by have hh:fullTwoTargetLogCap d β≤A:=by
            have hcaps:=fullRestrictionLogCap_properties d β
            have hfac:1≤((2*(finiteOmega d+2)+1:ℕ):ℝ):=by exact_mod_cast (show 1≤2*(finiteOmega d+2)+1 by omega)
            have hbase:0≤fullTwoTargetLogCap d β:=by
              unfold fullTwoTargetLogCap filledEndpointLogCap
              have ho:=sourceObservationLogCap_nonnegative d hd β hβ.le
              positivity
            exact (le_mul_of_one_le_left hbase hfac).trans hcaps.2.2.1
          exact hh) hL0))
    hcapture C hC row hcol hprior hpair
    (by simpa only [one_mul,mul_one,w] using budgets.1)
  let ix:I:=⟨xl,Or.inr (Or.inl rfl)⟩
  let iy:I:=⟨yl,Or.inr (Or.inr rfl)⟩
  exact (hfinal ix iy).trans (by simpa only [mul_one] using budgets.2)

end RegularGraph
end LocalLaw
