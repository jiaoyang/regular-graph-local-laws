import LocalLaw.PureModelSurgery
import LocalLaw.SourceEndpointStability
import LocalLaw.SwitchedEndpointBudget
import LocalLaw.AugmentedEndpointStability

/-! Actual exponential endpoint matching for a switched augmented model. -/
noncomputable section
set_option maxHeartbeats 2800000
namespace LocalLaw
local instance actualPureModelDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_actual_pure_model_matching (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      let gnew:=g.labelledResampledGraph T labels samples selector
      ∀ (S : Set (Tᶜ : Set (Fin N))) (hcontain : s.endpointModelVertices selector r⊆S),
      ((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget →
      ∀ RS : ℕ, (∀ u v,((g.deficient.delete T).restrict S).graph.dist u v≤RS) →
      let e:=g.augmentedEndpointEmbedding T labels samples selector r S hcontain
      ∀ i j : s.endpointModelRoots selector,
      ‖((gnew.deficient.delete T).restrict S).extensionGreen (semicircleRoot z) z (e i) (e j)-
        g.sourceEndpointQ T labels samples selector r (semicircleRoot z) z i j‖≤
        4*(1+endpointSurgeryModelRowCap d (2*(finiteOmega d+1))*endpointSurgeryCouplingCap d)^2*
          physicalModelTailConstant d*physicalTransfer d z^(2*r) := by
  let m:=2*(finiteOmega d+1)
  let C:=endpointSurgeryModelRowCap d m
  let w:=endpointSurgeryCouplingCap d
  let D:=2*physicalModelTailConstant d*C1^2
  have hCextra:=finiteExtraReferenceConstant_ge_one d hd
  have hC : 0≤C := by dsimp only [C,endpointSurgeryModelRowCap]; positivity
  have hw : 0≤w := by dsimp only [w,endpointSurgeryCouplingCap]; positivity
  have htail : 0≤physicalModelTailConstant d := by
    have hdR : (3:ℝ)≤d := Nat.cast_le.mpr hd
    have hden : 0<(d:ℝ)-1 := by linarith
    unfold physicalModelTailConstant DeficientGraph.localizationExceptionalMass
    positivity
  have hD : 0≤D := by dsimp only [D]; positivity
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_endpoint_surgery_smallness a b d β C w D ha hb hd hβ hC hw hD,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)]
    with N hnum hsmall hmargin hdepth
  intro g o z hz hfloor Cq badCount hplus ι _ labels samples
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let R:=logarithmicRadius (c/4) d N
  let selector:=R/4
  let r:=effectiveModelRadius a d N β
  let T:=graphBallVertices g.graph o ell
  let s:=g.admissibleState T labels samples
  let K:=s.endpointModelVertices selector r
  let f:=s.endpointModelRootEmbedding selector
  let eK:=s.endpointModelKernelEmbedding selector r
  let old:=g.deficient.delete T
  let gnew:=g.labelledResampledGraph T labels samples selector
  let new:=gnew.deficient.delete T
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let L:=Real.log (N:ℝ)
  intro S hcontain hOldS RS hRS
  have hell : ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hcentral : ell+r+1≤R/8 := by dsimp only [ell,r,R]; omega
  have hsep : 2*r+2≤selector := by dsimp only [r,selector,R]; omega
  have hOldK:=g.endpointModel_component_budget o ell selector r (R/8) hcentral hsep (hplus.structural.1 o) labels samples
  have hNewK:=g.switchedEndpointModel_component_budget hd o ell selector r (R/8) hcentral hsep (hplus.structural.1 o) labels samples
  have hOldCount:=g.endpointModel_old_component_root_count o ell selector r (R/8) (finiteOmega d)
    hcentral hsep (hplus.structural.1 o) labels samples
  have hNewCount : ∀ c : (new.restrict K).graph.ConnectedComponent,
      Nat.card {i : s.endpointModelRoots selector // eK i ∈ c.supp} ≤ m := by
    intro cc
    exact s.endpoint_post_root_count o ell selector r (R/8) (finiteOmega d) rfl hsep hcentral (hplus.structural.1 o) cc
  have hOldDiam:=s.endpointModel_old_distance_bound selector r m (by dsimp only [m]; omega) hOldCount
  have hNewDiam:=s.endpointModel_new_distance_bound selector r m (by dsimp only [m]; omega) hNewCount
  have hgraph : ∀ x y,x∉Set.range f ∨ y∉Set.range f→(old.graph.Adj x y↔new.graph.Adj x y) := by
    intro x y hxy
    have ha:=hxy.imp
      (fun hx hs=>hx ⟨⟨x,s.fullResampleOutsideEndpoints_subset_modelRoots selector hs⟩,rfl⟩)
      (fun hy hs=>hy ⟨⟨y,s.fullResampleOutsideEndpoints_subset_modelRoots selector hs⟩,rfl⟩)
    rcases ha with hx | hy
    · exact (s.fullResample_outside_adj_of_away_left selector x y hx).symm
    · rw [old.graph.adj_comm,new.graph.adj_comm]
      exact (s.fullResample_outside_adj_of_away_left selector y x hy).symm
  have num:=hnum z hz hfloor
  have hε : 0≤ε:=num.error_nonnegative
  have hp : ε≤L^3*ε := le_mul_of_one_le_left hε (one_le_pow₀ num.log_one)
  have hδ : 2*physicalModelTailConstant d*physicalTransfer d z^(2*r)≤D*g.sourcePrime a (logarithmicRadius β d N) z := by
    calc
      _ ≤ 2*physicalModelTailConstant d*(C1^2*ε) := mul_le_mul_of_nonneg_left num.tail (by positivity)
      _ ≤ 2*physicalModelTailConstant d*(C1^2*(L^3*ε)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hp (sq_nonneg C1)) (by positivity)
      _ = _ := by unfold D sourcePrime inflatedPrime; ring
  have hsmall' : (Fintype.card (s.endpointModelRoots selector):ℝ)*(1+C*w)*w*
      (2*physicalModelTailConstant d*physicalTransfer d z^(2*r))≤1/2 := by
    have hh:=hsmall g o ell hell labels samples selector z hz hfloor
    apply (mul_le_mul_of_nonneg_left hδ (by positivity)).trans
    simpa only [Nat.card_eq_fintype_card] using hh
  exact old.two_restriction_physical_surgery new hd S K f
    (fun i=>hcontain (eK i).property) (fun i=>(eK i).property)
    (g.deleted_degree_deficit_saturated T) (gnew.deleted_degree_deficit_saturated T) hgraph hOldS hOldK hNewK
    RS (m*(2*r+1)) (m*(2*r+1)) r m hRS hOldDiam hNewDiam
    (fun i v hv=>hcontain ⟨i.val,i.property,hv⟩) (fun i v hv=>⟨i.val,i.property,hv⟩)
    hNewCount z hz hsmall'

end RegularGraph
end LocalLaw
