import SpectralConsequences.TruncatedRootRowIdentity
import LocalLaw.SourceRetainedRowProfile

/-! Actual source budgets for the unexpanded truncated full-root model. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceTruncatedRootProfileDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_truncated_root_profile (a b d:ℕ) (c β B C1:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c)
    (hβ:0<β) (hβc:β≤c/32) (hC1:1≤C1):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→∀Cq badCount:ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z→
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      Nonempty (BoundaryMaxProfile ((g.deficient.restrict T).extensionGreen (g.Q z) z)
        (truncatedBoundaryInner g T (Equiv.refl _)) (cavityBallRoot g.graph o ell)
        a (Real.log (N:ℝ)) ((d:ℝ)*((d:ℝ)+1))
        (2*finiteExtraReferenceConstant d*((d:ℝ)+1))
        (8*(d:ℝ)*finiteExtraReferenceConstant d^2*sourceObservationLogCap d β)):=by
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_resampling_radius_margin a d 3 6 β hd hβ,hdepth]
    with N hnum hmargin hroom hdepth
  intro g o z hz hfloor Cq badCount hplus
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let r:=effectiveModelRadius a d N β
  let T:=graphBallVertices g.graph o ell
  let R:=logarithmicRadius (c/4) d N
  let M:=g.deficient.restrict T
  let Robs:=singletonObservationDiameter d r
  let L:=Real.log (N:ℝ)
  let A:=sourceObservationLogCap d β
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let C:=finiteExtraReferenceConstant d
  let n:ℝ:=Nat.card (BoundaryOrientedEdge g.graph T)
  let W:=8*(d:ℝ)*C^2*((Robs:ℝ)+1)
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepth).2
  have hcentral:ell≤R/8:=by dsimp only [ell,r,R];omega
  have hellr:ell+1≤r:=by
    change ell+1≤logarithmicRadius β d N-(2*doubleLogRadius a d N+4)
    omega
  have hconn:M.graph.Connected:=graphBall_connected g.graph o ell
  have hbase:(∑v,M.deficit v)+graphExcess M.graph≤finiteOmega d:=by
    have hzero:∀v,M.deficit v=0:=fun _=>rfl
    simp only [hzero,Finset.sum_const_zero,zero_add]
    exact (graphBallExcess_mono_radius g.graph o hcentral).trans (hplus.structural.1 o)
  have hbudget:M.ComponentFiniteReferenceBudget:=fun cc=>
    M.restrict_finiteReferenceBudget cc.supp hconn cc.connected_induce_supp (Or.inl hbase)
  have hdiam:∀u v,M.graph.dist u v≤Robs:=by
    intro u v
    apply (graphBall_distance_le_twice_radius g.graph o ell u v).trans
    dsimp only [Robs,singletonObservationDiameter]
    nlinarith only [hellr,Nat.zero_le (finiteOmega d)]
  have num:=hnum z hz hfloor
  have hprior:=hplus.cavity.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative hC1)
  have hfeedback:=(DeficientGraph.weak_localization_feedback_budgets d hd z (g.Q z) hz B (C1^2*ε) L A
    (mul_nonneg (sq_nonneg C1) num.error_nonnegative) num.log_one num.log_cap_nonnegative num.error_scaled
    hprior Robs (4*r+1) num.diameter_log num.pair_log num.localization_large).1
  have hp:=g.boundary_model_max_budgets hd T hbudget o ell (Set.Subset.refl _) (g.Q z) z hz
    (g.Q_im_nonnegative z hz) Robs hdiam hfeedback
  have hC:0≤C:=(by norm_num:(0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have ht:0≤physicalTransfer d z:=(physicalTransfer_pos d hd z).le
  refine ⟨⟨2*C*physicalTransfer d z^ell,Real.sqrt (n*W),W,by positivity,
    Real.sqrt_nonneg _,by dsimp only [W];positivity,hp.1,hp.2.1,?_,?_,?_,?_⟩⟩
  · simpa only [n,Nat.card_eq_fintype_card] using hp.2.2.1.le
  · simpa only [Nat.card_eq_fintype_card] using hp.2.2.2
  · simpa only [Nat.card_eq_fintype_card] using
      g.boundary_card_log_bound o a ell hd num.log_one hell
  · exact (mul_le_mul_of_nonneg_left num.diameter_log (show 0≤8*(d:ℝ)*C^2 by positivity)).trans_eq
      (by dsimp only [W,A,C,L];ring)

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_source_truncated_root_profile
