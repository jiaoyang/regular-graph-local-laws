import LocalLaw.SourceRetainedEntries
import LocalLaw.DeterministicCentralBudget
import LocalLaw.BoundaryWeightParameters

/-! # Actual fixed reference entry caps and the nine-log root gain -/

noncomputable section
namespace LocalLaw
local instance sourceRetainedEntryBoundsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_retained_entry_bounds (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      let ell := actualCavityDepth a d N z-1
      let r := effectiveModelRadius a d N β
      let T := graphBallVertices g.graph o ell
      let P := g.sourceRetainedReference T r (g.Q z) z
      let root : T := ⟨o,center_mem_graphBall g.graph o ell⟩
      (∀ x y, ‖P x y‖≤2*finiteExtraReferenceConstant d) ∧
        (∀ α, ‖P root (cutInsideVertex g.graph T α)‖≤2*finiteExtraReferenceConstant d/Real.log (N:ℝ)^9) := by
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
  let root : S := ⟨o,hS (center_mem_graphBall g.graph o ell)⟩
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let L := Real.log (N:ℝ)
  let A := sourceObservationLogCap d β
  let Robs := singletonObservationDiameter d r
  let C := finiteExtraReferenceConstant d
  have hC : 0≤C := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have ht : 0≤physicalTransfer d z := (physicalTransfer_pos d hd z).le
  have htone : physicalTransfer d z≤1 := by nlinarith [physicalTransfer_sq_le_half d hd z]
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
  have hkernel (u v : S) : ‖model.extensionGreen (g.Q z) z u v‖≤2*C*physicalTransfer d z^model.graph.dist u v :=
    model.componentwise_finite_kernel_decay hd hbudget (g.Q z) z hz (g.Q_im_nonnegative z hz) Robs hdiam hfeedback u v
  constructor
  · intro x y
    rw [g.sourceRetainedReference_entry_expanded_ball o ell r (g.Q z) z x y]
    exact (hkernel _ _).trans (mul_le_of_le_one_right (by positivity) (pow_le_one₀ ht htone))
  · intro α
    rw [g.sourceRetainedReference_entry_expanded_ball o ell r (g.Q z) z]
    have hh := hkernel root (inducedBoundaryInner g.graph o ell S hS α)
    have hdist : model.graph.dist root (inducedBoundaryInner g.graph o ell S hS α)=ell :=
      induced_boundary_inner_distance g.graph o ell S hS α
    rw [hdist] at hh
    have hL : 0<L := by have h := num.log_one; dsimp only [L]; linarith
    have hgain := selected_radius_decay_gain a d N z ha hd num.log_one
    have htail : physicalTransfer d z^ell≤(L^9)⁻¹ :=
      (physicalTransfer_resampling_gain d ell hd z).trans
        ((inv_le_inv₀ (resamplingDecayDenominator_pos d ell hd) (pow_pos hL 9)).mpr hgain)
    exact hh.trans ((mul_le_mul_of_nonneg_left htail (by positivity)).trans_eq (by ring))

end RegularGraph
end LocalLaw
