import LocalLaw.SourcePartialReferenceBounds

/-! # The actual old geometry behind every partial switched model -/

open Filter
noncomputable section
namespace LocalLaw
local instance sourcePartialGeometryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_partial_geometry (a d : ℕ) (c β : ℝ)
    (ha : 0<a) (hd : 3≤d) (hc : 0<c) (hβ : 0<β) (hβc : β≤c/32) :
    ∀ᶠ N : ℕ in atTop,∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      (∀ v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : ((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      let D:=hereditaryReferenceRadius d (augmentedObservationDiameter d r)
      ∀ S : Set (Tᶜ:Set (Fin N)), S⊆s.twoTargetEndpointVertices selector r x y →
      ((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget ∧
      (∀ u v,((g.deficient.delete T).restrict S).graph.dist u v≤D) ∧
      (D:ℝ)+1≤sourcePartialObservationLogCap d β*Real.log (N:ℝ) := by
  have hdepth:=(lowerLogLogRadius_tendsto a d ha hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_old_twoTarget_geometry a d c β hd hc hβ hβc,hdepth]
    with N hgeometry hdepthN
  intro g o z hballs ι _ labels samples x y
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let Saug:=s.twoTargetEndpointVertices selector r x y
  let D:=augmentedObservationDiameter d r
  let R:=hereditaryReferenceRadius d D
  let F:=2*(finiteOmega d:ℝ)+5
  have hF:1≤F := by
    dsimp only [F]
    have hh:=Nat.cast_nonneg (α:=ℝ) (finiteOmega d)
    linarith
  have hell:ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hgeo:=hgeometry g o ell hell hballs labels samples x y
  have hRgeom:(R:ℝ)+1≤F*((D:ℝ)+1) := by
    dsimp only [R,hereditaryReferenceRadius,F]
    push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) (finiteOmega d),Nat.cast_nonneg (α:=ℝ) D]
  have hRlog:(R:ℝ)+1≤sourcePartialObservationLogCap d β*Real.log (N:ℝ) :=
    hRgeom.trans ((mul_le_mul_of_nonneg_left hgeo.2.2 (by linarith : 0≤F)).trans_eq (by
      dsimp only [sourcePartialObservationLogCap,F]
      ring))
  intro S hSS
  exact ⟨(g.deficient.delete T).subset_restriction_component_budget Saug S hSS hgeo.1,
    (g.deficient.delete T).subset_finite_class_intrinsic_diameter Saug S hSS hgeo.1 D hgeo.2.1,hRlog⟩

end RegularGraph
end LocalLaw
