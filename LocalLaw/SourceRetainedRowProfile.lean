import LocalLaw.ActualBoundaryRowBudgets
import LocalLaw.BoundaryMaxProfile
import LocalLaw.SourceObservationParameters
import LocalLaw.TreeRadiusStability

/-!
# The actual fixed expanded-ball model supplies every maximum row profile

The enlarged source event realizes model class, diameter and boundary
feedback. All column sums, root decay/count cancellation and logarithmic
counts are conclusions, including the endpoint beta=c/32.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceRetainedRowProfileDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_retained_row_profile (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      let ell := actualCavityDepth a d N z-1
      let r := effectiveModelRadius a d N β
      let S := graphBallVertices g.graph o (ell+r+1)
      let hS : graphBallVertices g.graph o ell ⊆ S := graphBallVertices_mono g.graph o (by omega)
      let root : S := ⟨o,hS (center_mem_graphBall g.graph o ell)⟩
      Nonempty (BoundaryMaxProfile ((g.deficient.restrict S).extensionGreen (g.Q z) z)
        (inducedBoundaryInner g.graph o ell S hS) root a (Real.log (N:ℝ))
        ((d:ℝ)*((d:ℝ)+1)) (2*finiteExtraReferenceConstant d*((d:ℝ)+1))
        (8*(d:ℝ)*finiteExtraReferenceConstant d^2*sourceObservationLogCap d β)) := by
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_resampling_radius_margin a d 3 6 β hd hβ,hdepth] with N hnum hmargin hroom hdepth
  intro g o z hz hfloor Cq badCount hplus
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let r := effectiveModelRadius a d N β
  let R := logarithmicRadius (c/4) d N
  let S := graphBallVertices g.graph o (ell+r+1)
  let hS : graphBallVertices g.graph o ell ⊆ S := graphBallVertices_mono g.graph o (by omega)
  let model := g.deficient.restrict S
  let root : S := ⟨o,hS (center_mem_graphBall g.graph o ell)⟩
  let l := inducedBoundaryInner g.graph o ell S hS
  let C := finiteExtraReferenceConstant d
  let Robs := singletonObservationDiameter d r
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let L := Real.log (N:ℝ)
  let A := sourceObservationLogCap d β
  let n := (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)):ℝ)
  let M := 2*C*physicalTransfer d z^ell
  let W := 8*(d:ℝ)*C^2*((Robs:ℝ)+1)
  have hell : ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hcentral : ell+r+1≤R/8 := by dsimp only [ell,r,R]; omega
  have hellr : ell+1≤r := by
    change ell+1 ≤ logarithmicRadius β d N-(2*doubleLogRadius a d N+4)
    omega
  have hconn : model.graph.Connected := graphBall_connected g.graph o (ell+r+1)
  have hbase : (∑ v,model.deficit v)+graphExcess model.graph≤finiteOmega d := by
    have hz0 : ∀ v,model.deficit v=0 := fun _ => rfl
    simp only [hz0,Finset.sum_const_zero,zero_add]
    change graphBallExcess g.graph o (ell+r+1)≤finiteOmega d
    exact (graphBallExcess_mono_radius g.graph o hcentral).trans (hplus.structural.1 o)
  have hbudget : model.ComponentFiniteReferenceBudget := fun cc =>
    model.restrict_finiteReferenceBudget cc.supp hconn cc.connected_induce_supp (Or.inl hbase)
  have hdiam : ∀ u v,model.graph.dist u v≤Robs := by
    intro u v
    have hh := graphBall_distance_le_twice_radius g.graph o (ell+r+1) u v
    apply hh.trans
    dsimp only [Robs,singletonObservationDiameter]
    nlinarith only [hellr,Nat.zero_le (finiteOmega d)]
  have num := hnum z hz hfloor
  have hscaled : 0≤C1^2*ε := mul_nonneg (sq_nonneg C1) num.error_nonnegative
  have hprior := hplus.cavity.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative hC1)
  have hfeedback := (DeficientGraph.weak_localization_feedback_budgets d hd z (g.Q z) hz B (C1^2*ε) L A
    hscaled num.log_one num.log_cap_nonnegative num.error_scaled hprior Robs (4*r+1)
      num.diameter_log num.pair_log num.localization_large).1
  have hp := g.boundary_model_max_budgets hd S hbudget o ell hS (g.Q z) z hz (g.Q_im_nonnegative z hz)
    Robs hdiam hfeedback
  have hC : 0≤C := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hn : 0≤n := Nat.cast_nonneg _
  have ht : 0≤physicalTransfer d z := (physicalTransfer_pos d hd z).le
  have hM : 0≤M := by dsimp only [M]; positivity
  have hW : 0≤W := by dsimp only [W]; positivity
  refine ⟨⟨M,Real.sqrt (n*W),W,hM,Real.sqrt_nonneg _,hW,hp.1,hp.2.1,?_,?_,?_,?_⟩⟩
  · simpa only [n,Nat.card_eq_fintype_card] using hp.2.2.1.le
  · simpa only [Nat.card_eq_fintype_card] using hp.2.2.2
  · simpa only [Nat.card_eq_fintype_card] using g.boundary_card_log_bound o a ell hd num.log_one hell
  · have hh := mul_le_mul_of_nonneg_left num.diameter_log (show 0≤8*(d:ℝ)*C^2 by positivity)
    exact hh.trans_eq (by dsimp only [W,A,C,L]; ring)

end RegularGraph
end LocalLaw
