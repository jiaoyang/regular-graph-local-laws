import SpectralConsequences.SourceProtectedPatches
import LocalLaw.ResamplingStructuralCost

/-! Source probability and deterministic bad-count clauses for switch exit. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceLargePatchProbabilityDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}

/-- The exact large-patch data used in the deterministic exit lemma holds
under the actual local sampling law with a fixed positive polynomial gap. -/
theorem eventually_source_protectedPatches_probability (a d:ℕ)(cAux γ:ℝ)
    (ha:0<a)(hd:3≤d)(hc:0<cAux)(hγc:cAux/2≤γ)(hγ:γ<1):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      let ell:=actualCavityDepth a d N z-1
      let R:=logarithmicRadius (cAux/16) d N
      LargeTreeCountAux cAux γ g→(graphBall g.graph o R).IsTree→
      ∀{ι:Type*}[Fintype ι]
      (boundary:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)),
      eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o ell))
        (fun S=>¬LabelledResamplingState.ProtectedPatches
          (g.admissibleState (graphBallVertices g.graph o ell) boundary S) (R/4) R)≤
        1/(N:ℝ)^((1-γ)/2):=by
  have hdepth:=(lowerLogLogRadius_tendsto a d ha hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_source_protectedPatches a d cAux ha hd hc,
    eventually_allLargeSampleGood_failure a d cAux γ hd hc.le hγc hγ,hdepth]
    with N hgeom hprob hdepth
  intro g o z
  dsimp only
  intro haux hTree ι _ boundary
  apply (eventMass_mono (localSamplingWeight g.graph _) finiteUniformWeight_nonneg ?_).trans
    (hprob g o _ (actualCavityDepth_radius_bounds a d N z hdepth).2 haux)
  intro S hS hgood
  exact hS (hgeom g o z hTree boundary S hgood)

/-- Bad-count inflation is bounded for every actual sample, independently
of the protected-patch event. The factor2 is part of the auxiliary event. -/
theorem eventually_source_work_bad_count (a d:ℕ)(cAux γ:ℝ)
    (ha:0<a)(hd:3≤d)(hc:0<cAux)(hγc:cAux/2≤γ):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      let ell:=actualCavityDepth a d N z-1
      let R:=logarithmicRadius (cAux/16) d N
      LargeTreeCountAux cAux γ g→∀{ι:Type*}[Fintype ι]
      (boundary:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
      (S:LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)),
      (nonTreeCenters ((g.admissibleState (graphBallVertices g.graph o ell) boundary S).fullResample (R/4)).graph R).card≤
        2*⌊(N:ℝ)^γ⌋₊:=by
  have hdepth:=(lowerLogLogRadius_tendsto a d ha hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [LocalLaw.RegularGraph.eventually_resampling_badCenter_cost a d (cAux/4) γ hd (by positivity) (by linarith),
    hdepth,Filter.eventually_ge_atTop 1] with N hcost hdepth hN
  intro g o z
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let R:=logarithmicRadius (cAux/16) d N
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepth).2
  have hR: R≤2*logarithmicRadius (cAux/4) d N+1:=by
    have hh:=logarithmicRadius_nat_mul_lower 4 d N (cAux/16) hd hN (by positivity)
    rw [show ((4:ℕ):ℝ)*(cAux/16)=cAux/4 by norm_num;ring] at hh
    dsimp only [R]
    omega
  intro haux ι _ boundary S
  let s:=g.admissibleState (graphBallVertices g.graph o ell) boundary S
  have hbad:(nonTreeCenters g.graph R).card≤⌊(N:ℝ)^γ⌋₊:=
    (Finset.card_le_card (nonTreeCenters_mono g.graph hR)).trans haux
  have hbudget:=hcost g o ell hell
  rw [show (cAux/4)/4=cAux/16 by ring] at hbudget
  exact s.fullResample_badCount_twice (R/4) d R _ hd (fun v=>(g.regular v).le) hbad hbudget

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_source_protectedPatches_probability
#print axioms SpectralConsequences.RegularGraph.eventually_source_work_bad_count
