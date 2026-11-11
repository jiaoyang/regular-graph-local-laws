import SpectralConsequences.ProtectedSameRadiusLocalization
import SpectralConsequences.WorkTreeCountAuxiliary
import LocalLaw.SourceResamplingStructural

/-! Source-(7.31) geometric exit, at a smaller work exponent.

Both count auxiliaries are actual graph events with every polynomial tail.
The target structural event has exactly the ORIGINAL work bad-count exponent.
No switching stability or sampling probability is assumed.
-/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceGeometricSwitchExitDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_geometric_switch_exit (a d ω:ℕ)(cAux γ δ:ℝ)
    (ha:0<a)(hd:3≤d)(hc:0<cAux)(hγc:cAux/2≤γ)(hγ:γ<1)
    (hδ:3*cAux/16<δ)(hδ1:δ<cAux/4):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      let ell:=actualCavityDepth a d N z-1
      let R:=logarithmicRadius (cAux/16) d N
      LargeTreeCountAux cAux γ g→WorkTreeCountAux cAux δ g→
      (∀v,graphBallExcess g.graph v R≤ω)→(graphBall g.graph o R).IsTree→
      ∀{ι:Type*}[Fintype ι]
      (boundary:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)),
      eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o ell))
        (fun S=>let h:=g.labelledResampledGraph (graphBallVertices g.graph o ell) boundary S (R/4)
          ¬LocalLaw.RegularGraph.structural R ω ⌊(N:ℝ)^(cAux/4)⌋₊ h ∨
            ¬(graphBall h.graph o R).IsTree)≤1/(N:ℝ)^((1-γ)/2):=by
  filter_upwards [eventually_source_protectedPatches_probability a d cAux γ ha hd hc hγc hγ,
    eventually_source_original_work_bad_count a d cAux δ ha hd hc hδ hδ1]
    with N hprob hbad
  intro g o z
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let R:=logarithmicRadius (cAux/16) d N
  intro hLarge hSmall hOld hTree ι _ boundary
  apply (eventMass_mono (localSamplingWeight g.graph _) finiteUniformWeight_nonneg ?_).trans
    (hprob g o z hLarge hTree boundary)
  intro S hExit hP
  let T:=graphBallVertices g.graph o ell
  let s:=g.admissibleState T boundary S
  let h:=g.labelledResampledGraph T boundary S (R/4)
  have hnewStructural:LocalLaw.RegularGraph.structural R ω ⌊(N:ℝ)^(cAux/4)⌋₊ h:=by
    refine ⟨?_,?_⟩
    · exact hP.same_radius_excess ω hOld
    · exact hbad g o z hSmall boundary S
  have hnewTree:(graphBall h.graph o R).IsTree:=
    hP.same_radius_root_tree o (center_mem_graphBall g.graph o ell) hTree
  exact hExit.elim (fun hn=>hn hnewStructural) (fun hn=>hn hnewTree)

/-- One concrete choice has a positive fixed gap and needs no exponent
selection certificate: cAux≤1/4 gives PG(exit)≤N^(-9/32). -/
theorem eventually_source_geometric_switch_exit_concrete (a d ω:ℕ)(cAux:ℝ)
    (ha:0<a)(hd:3≤d)(hc:0<cAux)(hc1:cAux≤1/4):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      let ell:=actualCavityDepth a d N z-1
      let R:=logarithmicRadius (cAux/16) d N
      LargeTreeCountAux cAux (7*cAux/4) g→WorkTreeCountAux cAux (7*cAux/32) g→
      (∀v,graphBallExcess g.graph v R≤ω)→(graphBall g.graph o R).IsTree→
      ∀{ι:Type*}[Fintype ι]
      (boundary:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)),
      eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o ell))
        (fun S=>let h:=g.labelledResampledGraph (graphBallVertices g.graph o ell) boundary S (R/4)
          ¬LocalLaw.RegularGraph.structural R ω ⌊(N:ℝ)^(cAux/4)⌋₊ h ∨
            ¬(graphBall h.graph o R).IsTree)≤1/(N:ℝ)^(9/32:ℝ):=by
  filter_upwards [eventually_source_geometric_switch_exit a d ω cAux (7*cAux/4) (7*cAux/32)
    ha hd hc (by linarith) (by linarith) (by linarith) (by linarith),
    Filter.eventually_ge_atTop 1] with N hN hN1
  intro g o z
  dsimp only
  intro hLarge hSmall hOld hTree ι _ boundary
  apply (hN g o z hLarge hSmall hOld hTree boundary).trans
  apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_source_geometric_switch_exit_concrete
