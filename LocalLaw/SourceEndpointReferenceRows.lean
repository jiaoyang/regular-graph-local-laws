import LocalLaw.ActualSourceEndpointStability
import LocalLaw.SourceEndpointMatrices

/-! # Realized source row and column sums of the canonical post endpoint model -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceEndpointReferenceRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_endpoint_reference_rows (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ‖z‖ ≤ B → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      let selector := logarithmicRadius (c / 4) d N / 4
      let r := effectiveModelRadius a d N β
      let Q := g.sourceEndpointQ T boundary samples selector r (g.Q z) z
      (∀ i, ∑ j, ‖Q i j‖ ≤ endpointSurgeryModelRowCap d (2 * (finiteOmega d + 1))) ∧
        (∀ j, ∑ i, ‖Q i j‖ ≤ endpointSurgeryModelRowCap d (2 * (finiteOmega d + 1))) := by
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc, hdepth]
    with N hnum hmargin hdepth
  intro g o z hz hscale _ Cq badCount hplus ι _ boundary samples
  dsimp only
  let ell := actualCavityDepth a d N z - 1
  let R := logarithmicRadius (c / 4) d N
  let selector := R / 4
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  let M := g.switchedEndpointModel T boundary samples selector r
  let e := s.endpointModelKernelEmbedding selector r
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  have num := hnum z hz hscale
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hcentral : ell + r + 1 ≤ R / 8 := by dsimp only [ell, r, R]; omega
  have hsep : 2 * r + 2 ≤ selector := by dsimp only [r, selector, R]; omega
  have hpost : M.ComponentFiniteReferenceBudget := g.switchedEndpointModel_component_budget hd o ell selector r (R / 8)
    hcentral hsep (hplus.structural.1 o) boundary samples
  have hcount : ∀ cc : M.graph.ConnectedComponent,
      Nat.card {i : s.endpointModelRoots selector // e i ∈ cc.supp} ≤ 2 * (finiteOmega d + 1) := by
    intro cc
    exact s.endpoint_post_root_count o ell selector r (R / 8) (finiteOmega d) rfl hsep hcentral
      (hplus.structural.1 o) cc
  have hdiam : ∀ x y, M.graph.dist x y ≤ singletonObservationDiameter d r := fun x y =>
    (s.endpointModel_new_distance_bound selector r (2 * (finiteOmega d + 1)) (by omega) hcount x y).trans
      (endpoint_component_diameter_le_observation d r)
  have hε : 0 ≤ ε := num.error_nonnegative
  have hprior := hplus.cavity.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) hε hC1)
  have hfeedback := (DeficientGraph.weak_localization_feedback_budgets d hd z (g.Q z) hz B
    (C1 ^ 2 * ε) (Real.log (N : ℝ)) (sourceObservationLogCap d β) (mul_nonneg (sq_nonneg C1) hε)
      num.log_one num.log_cap_nonnegative num.error_scaled hprior (singletonObservationDiameter d r)
        (4 * r + 1) num.diameter_log num.pair_log num.localization_large).1
  have hh := M.componentwise_endpoint_green_rows hd hpost e (2 * (finiteOmega d + 1)) hcount
    (g.Q z) z hz (g.Q_im_nonnegative z hz) (singletonObservationDiameter d r) hdiam hfeedback
  exact ⟨fun i => hh.1 (e i), fun j => hh.2 (e j)⟩

end RegularGraph
end LocalLaw
