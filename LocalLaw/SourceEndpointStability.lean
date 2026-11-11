import LocalLaw.RestrictedSurgeryStability
import LocalLaw.OldEndpointComponentCounts
import LocalLaw.EndpointComponentCounts
import LocalLaw.DetachedEndpointModel
import LocalLaw.SourceSurgeryParameters
import LocalLaw.EndpointSurgeryParameters

/-!
# Realized source endpoint surgery from the actual enlarged event

Actual old/new root counts, common-model diameter, physical support and
source logarithmic budgets discharge every analytic condition in the finite
surgery theorem. The post-model finite class is kept explicit here until
its independent branch-restoration construction is supplied.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceEndpointStabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceEndpointErrorConstant (d : ℕ) (C1 : ℝ) : ℝ :=
  4 * (1 + endpointSurgeryModelRowCap d (2 * (finiteOmega d + 1)) * endpointSurgeryCouplingCap d) ^ 2 * C1

namespace RegularGraph

theorem eventually_source_endpoint_surgery_of_post_budget (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ‖z‖ ≤ B → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1) (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      let selector := logarithmicRadius (c / 4) d N / 4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T boundary samples
      let e := s.endpointModelKernelEmbedding selector r
      let gnew := g.labelledResampledGraph T boundary samples selector
      (g.switchedEndpointModel T boundary samples selector r).ComponentFiniteReferenceBudget →
      ∀ i j : s.endpointModelRoots selector,
      ‖(gnew.deficient.delete T).G z i.val j.val -
        (g.switchedEndpointModel T boundary samples selector r).extensionGreen (g.Q z) z (e i) (e j)‖ ≤
        sourceEndpointErrorConstant d C1 * g.sourcePrime a (logarithmicRadius β d N) z := by
  let m := 2 * (finiteOmega d + 1)
  let C := endpointSurgeryModelRowCap d m
  let w := endpointSurgeryCouplingCap d
  have hC : 0 ≤ C := by
    dsimp only [C, endpointSurgeryModelRowCap]
    have hh := finiteExtraReferenceConstant_ge_one d hd
    positivity
  have hw : 0 ≤ w := by dsimp only [w, endpointSurgeryCouplingCap]; positivity
  have hC1p : 0 ≤ C1 := (by norm_num : (0 : ℝ) ≤ 1).trans hC1
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc, hdepth,
    eventually_endpoint_surgery_smallness a b d β C w (2 * C1) ha hb hd hβ hC hw (by positivity)]
    with N hnum hmargin hdepth hsmall
  intro g o z hz hfloor hzB Cq badCount hplus ι _ boundary samples
  dsimp only
  let ell := actualCavityDepth a d N z - 1
  let R := logarithmicRadius (c / 4) d N
  let selector := R / 4
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  let S := s.endpointModelVertices selector r
  let e := s.endpointModelKernelEmbedding selector r
  let gnew := g.labelledResampledGraph T boundary samples selector
  let old := g.deficient.delete T
  let new := gnew.deficient.delete T
  let Robs := singletonObservationDiameter d r
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let L := Real.log (N : ℝ)
  intro hpost
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hcentral : ell + r + 1 ≤ R / 8 := by dsimp only [ell, r, R]; omega
  have hsep : 2 * r + 2 ≤ selector := by dsimp only [selector, r, R]; omega
  have hOldBudget : (old.restrict S).ComponentFiniteReferenceBudget :=
    g.endpointModel_component_budget o ell selector r (R / 8) hcentral hsep (hplus.structural.1 o) boundary samples
  have hOldCount := g.endpointModel_old_component_root_count o ell selector r (R / 8) (finiteOmega d)
    hcentral hsep (hplus.structural.1 o) boundary samples
  have hNewCount : ∀ cc : (new.restrict S).graph.ConnectedComponent,
      Nat.card {i : s.endpointModelRoots selector // e i ∈ cc.supp} ≤ m := by
    intro cc
    exact s.endpoint_post_root_count o ell selector r (R / 8) (finiteOmega d) rfl hsep hcentral
      (hplus.structural.1 o) cc
  have hOldDiam : ∀ x y, (old.restrict S).graph.dist x y ≤ Robs := by
    intro x y
    exact (s.endpointModel_old_distance_bound selector r m (by dsimp only [m]; omega) hOldCount x y).trans
      (endpoint_component_diameter_le_observation d r)
  have hNewDiam : ∀ x y, (new.restrict S).graph.dist x y ≤ Robs := by
    intro x y
    exact (s.endpointModel_new_distance_bound selector r m (by dsimp only [m]; omega) hNewCount x y).trans
      (endpoint_component_diameter_le_observation d r)
  have hcapture : ∀ i, graphBallVertices old.graph (e i).val r ⊆ S := by
    intro i v hv
    exact ⟨i.val, i.property, hv⟩
  have hgraph : ∀ x y, x ∉ Set.range (fun i => (e i).val) ∨ y ∉ Set.range (fun i => (e i).val) →
      (old.graph.Adj x y ↔ new.graph.Adj x y) := by
    intro x y hxy
    have haway : x ∉ s.fullResampleOutsideEndpoints selector ∨ y ∉ s.fullResampleOutsideEndpoints selector :=
      hxy.imp
        (fun hx hs => hx ⟨⟨x, s.fullResampleOutsideEndpoints_subset_modelRoots selector hs⟩, rfl⟩)
        (fun hy hs => hy ⟨⟨y, s.fullResampleOutsideEndpoints_subset_modelRoots selector hs⟩, rfl⟩)
    rcases haway with hx | hy
    · exact (s.fullResample_outside_adj_of_away_left selector x y hx).symm
    · rw [old.graph.adj_comm, new.graph.adj_comm]
      exact (s.fullResample_outside_adj_of_away_left selector y x hy).symm
  have num := hnum z hz hfloor
  have hsmall' : (Fintype.card (s.endpointModelRoots selector) : ℝ) * (1 + C * w) * w * (2 * C1 * L ^ 3 * ε) ≤ 1 / 2 := by
    have hh := hsmall g o ell hell boundary samples selector z hz hfloor
    simpa only [Nat.card_eq_fintype_card, sourcePrime, inflatedPrime, mul_assoc] using hh
  have happ : ∀ i j, ‖old.G z (e i).val (e j).val - old.P r z (g.Q z) (e i).val (e j).val‖ ≤ C1 * L ^ 3 * ε := by
    intro i j
    have hh := hplus.deleted (e i).val (e j).val
    simpa only [sourcePrime, inflatedPrime, mul_assoc] using hh
  have hfinal := old.restricted_endpoint_surgery_stability new hd S e r Robs Robs m z (g.Q z) hz
    (g.Q_im_nonnegative z hz) B C1 ε L (sourceObservationLogCap d β) hzB num
    (g.deleted_degree_deficit_saturated T) (gnew.deleted_degree_deficit_saturated T) hgraph
    hOldBudget hpost hOldDiam hNewDiam num.diameter_log num.diameter_log hcapture hNewCount hplus.cavity happ hsmall'
  intro i j
  exact (hfinal i j).trans_eq (by unfold sourceEndpointErrorConstant sourcePrime inflatedPrime; ring)

end RegularGraph
end LocalLaw
