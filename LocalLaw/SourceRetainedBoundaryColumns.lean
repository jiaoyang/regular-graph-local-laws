import LocalLaw.BoundaryInnerColumns
import LocalLaw.SourceRetainedEntryBounds

/-! # Actual fixed retained reference has logarithmic boundary columns -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceRetainedBoundaryColumnsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceRetainedBoundaryColumnConstant (d : ℕ) (β : ℝ) : ℝ :=
  boundaryInnerColumnConstant d*sourceObservationLogCap d β

namespace RegularGraph

theorem eventually_source_retained_boundary_columns (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop,∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z → ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell := actualCavityDepth a d N z-1
      let r := effectiveModelRadius a d N β
      let T := graphBallVertices g.graph o ell
      let P := g.sourceRetainedReference T r (g.Q z) z
      let l := fun α => cutInsideVertex g.graph T (labels α)
      ∀ j,∑ α,‖P (l α) (l j)‖≤sourceRetainedBoundaryColumnConstant d β*Real.log (N:ℝ) := by
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_resampling_radius_margin a d 3 6 β hd hβ,hdepth] with N hnum hmargin hroom hdepth
  intro g o z hz hfloor Cq badCount hplus ι _ labels
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let S := graphBallVertices g.graph o (ell+r+1)
  let hS : T⊆S := graphBallVertices_mono g.graph o (by omega)
  let model := g.deterministicCentralModel o ell r
  let P := g.sourceRetainedReference T r (g.Q z) z
  let K := model.extensionGreen (g.Q z) z
  let l := inducedBoundaryInner g.graph o ell S hS
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let L := Real.log (N:ℝ)
  let A := sourceObservationLogCap d β
  let Robs := singletonObservationDiameter d r
  have hC : 0≤boundaryInnerColumnConstant d := by
    have hh : 0≤finiteExtraReferenceConstant d := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
    dsimp only [boundaryInnerColumnConstant]; positivity
  have hell : ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hcentral : ell+r+1≤logarithmicRadius (c/4) d N/8 := by dsimp only [ell,r]; omega
  have hellr : ell≤r := by
    change ell≤logarithmicRadius β d N-(2*doubleLogRadius a d N+4)
    omega
  have hbudget := (g.sourceOmegaPlus_deterministicCentralModel_budget a r (logarithmicRadius β d N)
    (logarithmicRadius (c/4) d N) ell Cq badCount C1 o z hplus hcentral).1.to_componentFinite
  have hexcess : graphExcess model.graph≤finiteOmega d :=
    (graphBallExcess_mono_radius g.graph o hcentral).trans (hplus.structural.1 o)
  have hdiam : ∀ u v,model.graph.dist u v≤Robs := fun u v =>
    (g.deterministicCentralModel_distance_bound o ell r u v).trans (deterministicCentralModel_diameter_le_observation d ell r hellr)
  have num := hnum z hz hfloor
  have hprior := hplus.cavity.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative hC1)
  have hfeedback := (DeficientGraph.weak_localization_feedback_budgets d hd z (g.Q z) hz B (C1^2*ε) L A
    (mul_nonneg (sq_nonneg C1) num.error_nonnegative) num.log_one num.log_cap_nonnegative num.error_scaled
    hprior Robs (4*r+1) num.diameter_log num.pair_log num.localization_large).1
  have hcols := g.boundary_model_inner_columns hd S (g.deterministicCentralModel_connected o ell r)
    hbudget hexcess o ell hS (g.Q z) z hz (g.Q_im_nonnegative z hz) Robs hdiam hfeedback
  have hellR : (ell:ℝ)+1≤A*L :=
    (add_le_add_right (Nat.cast_le.mpr (by have hh := deterministicCentralModel_diameter_le_observation d ell r hellr; change 2*(ell+r+1)≤Robs at hh; omega : ell≤Robs)) 1).trans num.diameter_log
  intro j
  calc
    _ = ∑ α,‖K (l (labels α)) (l (labels j))‖ := by
      apply Finset.sum_congr rfl
      intro α _
      rw [g.sourceRetainedReference_entry_expanded_ball o ell r (g.Q z) z]
      rfl
    _ = ∑ α,‖K (l α) (l (labels j))‖ := labels.sum_comp (fun α => ‖K (l α) (l (labels j))‖)
    _ ≤ boundaryInnerColumnConstant d*((ell:ℝ)+1) := hcols (labels j)
    _ ≤ boundaryInnerColumnConstant d*(A*L) := mul_le_mul_of_nonneg_left hellR hC
    _ = _ := by dsimp only [sourceRetainedBoundaryColumnConstant,A,L]; ring

end RegularGraph
end LocalLaw
