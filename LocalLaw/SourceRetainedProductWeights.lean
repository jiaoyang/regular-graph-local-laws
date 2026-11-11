import LocalLaw.SourceRetainedEntryBounds
import LocalLaw.SourceFixedWeightConcentration
import LocalLaw.ActualLeadingDiagonalStrong

/-! # A deterministic finite family of all retained row-product weights -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceRetainedProductWeightsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

def sourceRetainedProductWeights (g : RegularGraph N d) (o : Fin N) (ell r : ℕ) (q z : ℂ) :
    graphBallVertices g.graph o ell → BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell) → ℂ :=
  fun y α => g.sourceRetainedReference (graphBallVertices g.graph o ell) r q z
      ⟨o, center_mem_graphBall g.graph o ell⟩ (cutInsideVertex g.graph _ α) *
    g.sourceRetainedReference (graphBallVertices g.graph o ell) r q z y (cutInsideVertex g.graph _ α)

theorem sourceRetainedProductWeights_eq_model (g : RegularGraph N d) (o : Fin N) (ell r : ℕ)
    (q z : ℂ) (y : graphBallVertices g.graph o ell)
    (α : BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) :
    let S := graphBallVertices g.graph o (ell+r+1)
    let hS := graphBallVertices_mono g.graph o (show ell≤ell+r+1 by omega)
    g.sourceRetainedProductWeights o ell r q z y α =
      g.deficient.boundaryProductWeight S o ell hS q z ⟨y.val,hS y.property⟩ α := by
  unfold sourceRetainedProductWeights
  rw [g.sourceRetainedReference_entry_expanded_ball, g.sourceRetainedReference_entry_expanded_ball]
  rfl

theorem eventually_source_retained_product_weight_bounds (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      let ell := actualCavityDepth a d N z-1
      let r := effectiveModelRadius a d N β
      let w := g.sourceRetainedProductWeights o ell r (g.Q z) z
      let L := Real.log (N:ℝ)
      let A := sourceObservationLogCap d β
      let D := resamplingDecayDenominator d ell
      ∀ y,
      (∑ α, ‖w y α‖)≤(8*(d:ℝ)*finiteExtraReferenceConstant d^2*A)*L ∧
      Real.sqrt (∑ α, ‖w y α‖^2)≤(32*(d:ℝ)*finiteExtraReferenceConstant d^4*A+1)*L/D ∧
      (∀ α, ‖w y α‖≤4*finiteExtraReferenceConstant d^2/D) := by
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_resampling_radius_margin a d 3 6 β hd hβ,hdepth] with N hnum hmargin hroom hdepth
  intro g o z hz hfloor Cq badCount hplus
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let S := graphBallVertices g.graph o (ell+r+1)
  let hS : T ⊆ S := graphBallVertices_mono g.graph o (by omega)
  let model := g.deterministicCentralModel o ell r
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let L := Real.log (N:ℝ)
  let A := sourceObservationLogCap d β
  let Robs := singletonObservationDiameter d r
  have hell : ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hcentral : ell+r+1≤logarithmicRadius (c/4) d N/8 := by dsimp only [ell,r]; omega
  have hellr : ell≤r := by
    change ell≤logarithmicRadius β d N-(2*doubleLogRadius a d N+4)
    omega
  have hbudget := (g.sourceOmegaPlus_deterministicCentralModel_budget a r (logarithmicRadius β d N)
    (logarithmicRadius (c/4) d N) ell Cq badCount C1 o z hplus hcentral).1.to_componentFinite
  have hdiam : ∀ u v,model.graph.dist u v≤Robs := fun u v =>
    (g.deterministicCentralModel_distance_bound o ell r u v).trans (deterministicCentralModel_diameter_le_observation d ell r hellr)
  have num := hnum z hz hfloor
  have hprior := hplus.cavity.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative hC1)
  have hfeedback := (DeficientGraph.weak_localization_feedback_budgets d hd z (g.Q z) hz B (C1^2*ε) L A
    (mul_nonneg (sq_nonneg C1) num.error_nonnegative) num.log_one num.log_cap_nonnegative num.error_scaled
    hprior Robs (4*r+1) num.diameter_log num.pair_log num.localization_large).1
  intro y
  have hh := g.deficient.boundaryProductWeight_log_bounds hd S hbudget o ell hS (g.Q z) z hz
    (g.Q_im_nonnegative z hz) Robs hdiam hfeedback A L num.log_cap_nonnegative num.log_one
    num.diameter_log ⟨y.val,hS y.property⟩
  have hw : g.deficient.boundaryProductWeight S o ell hS (g.Q z) z ⟨y.val,hS y.property⟩ =
      g.sourceRetainedProductWeights o ell r (g.Q z) z y := by
    funext α
    exact (g.sourceRetainedProductWeights_eq_model o ell r (g.Q z) z y α).symm
  rw [hw] at hh
  exact hh

end RegularGraph
end LocalLaw
