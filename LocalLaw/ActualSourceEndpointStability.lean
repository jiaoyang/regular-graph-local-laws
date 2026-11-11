import LocalLaw.SourceEndpointStability
import LocalLaw.SwitchedEndpointBudget

/-!
# Actual source endpoint stability with every geometric premise discharged

The independent branch-restoration proof supplies the post-model class.
Every remaining condition in the physical finite-rank comparison follows
from the actual source enlarged event and realized logarithmic parameters.
-/

noncomputable section
namespace LocalLaw
local instance actualSourceEndpointStabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_actual_source_endpoint_stability (a b d : ℕ) (c β B C1 : ℝ)
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
      ∀ i j : s.endpointModelRoots selector,
      ‖(gnew.deficient.delete T).G z i.val j.val -
        (g.switchedEndpointModel T boundary samples selector r).extensionGreen (g.Q z) z (e i) (e j)‖ ≤
        sourceEndpointErrorConstant d C1 * g.sourcePrime a (logarithmicRadius β d N) z := by
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_source_endpoint_surgery_of_post_budget a b d c β B C1
    ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc, hdepth]
    with N hstability hmargin hdepth
  intro g o z hz hfloor hzB Cq badCount hplus ι _ boundary samples
  dsimp only
  let ell := actualCavityDepth a d N z - 1
  let R := logarithmicRadius (c / 4) d N
  let r := effectiveModelRadius a d N β
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hcentral : ell + r + 1 ≤ R / 8 := by dsimp only [ell, r, R]; omega
  have hsep : 2 * r + 2 ≤ R / 4 := by dsimp only [r, R]; omega
  have hpost := g.switchedEndpointModel_component_budget hd o ell (R / 4) r (R / 8)
    hcentral hsep (hplus.structural.1 o) boundary samples
  exact hstability g o z hz hfloor hzB Cq badCount hplus boundary samples hpost

end RegularGraph
end LocalLaw
