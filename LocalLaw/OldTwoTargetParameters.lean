import LocalLaw.OldTwoTargetAugmentation

/-! Actual numerical realization of old two-target model geometry. -/
noncomputable section
namespace LocalLaw
local instance oldTwoTargetParametersDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_old_twoTarget_geometry (a d : ℕ) (c β : ℝ)
    (hd : 3 ≤ d) (hc : 0 < c) (hβ : 0 < β) (hβc : β ≤ c/32) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (ell : ℕ),
      ell ≤ doubleLogRadius a d N →
      (∀ v, graphBallExcess g.graph v (logarithmicRadius (c/4) d N) ≤ finiteOmega d) →
      ∀ {ι : Type}
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
      (x y : ((graphBallVertices g.graph o ell)ᶜ : Set (Fin N))),
      let T := graphBallVertices g.graph o ell
      let r := effectiveModelRadius a d N β
      let selector := logarithmicRadius (c/4) d N / 4
      let s := g.admissibleState T boundary samples
      let S := s.twoTargetEndpointVertices selector r x y
      ((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget ∧
      (∀ u v, ((g.deficient.delete T).restrict S).graph.dist u v ≤ augmentedObservationDiameter d r) ∧
      (augmentedObservationDiameter d r : ℝ)+1 ≤ sourceObservationLogCap d β * Real.log (N:ℝ) := by
  filter_upwards [eventually_effective_augmented_radius_margin a d c β hd hc hβ hβc,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_log_ge_nat 1] with N hmargin hcommon hL
  intro g o ell hell hballs ι boundary samples x y
  dsimp only
  let r := effectiveModelRadius a d N β
  let R := logarithmicRadius (c/4) d N
  have hm : 7*r+6*ell+8 ≤ R := hmargin ell hell
  have hs : 2*r+2 ≤ R/4 := by
    have hh := Nat.mul_le_mul_left 2 hcommon
    have hdiv : 2*(R/8) ≤ R/4 := by omega
    omega
  refine ⟨g.old_twoTargetEndpoint_component_budget o ell (R/4) r R hm hs hballs boundary samples x y, ?_, ?_⟩
  · exact g.old_twoTargetEndpoint_distance_bound hd o ell (R/4) r R (by omega) hs (hballs o) boundary samples x y
  · exact effective_augmented_diameter_log a d N β hd hβ.le hL

end RegularGraph
end LocalLaw
