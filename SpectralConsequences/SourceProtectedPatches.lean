import LocalLaw.AdmissibleGreenBlock
import SpectralConsequences.ProtectedSamplePatches
import SpectralConsequences.LargePatchAuxiliary

/-! Source-instantiated protected patches at a smaller moment work radius. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceProtectedPatchesDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}

theorem protectedPatches_of_source_tree (g:LocalLaw.RegularGraph N d)(o:Fin N)
    (ell selector R M:ℕ)(hmargin:ell+1+selector≤R)(hM:4*R+3≤M)
    (hsel:2*selector+1≤M)(hTree:(graphBall g.graph o R).IsTree)
    {ι:Type*}[Fintype ι]
    (boundary:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (S:LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (hS:AllLargeSampleGood g.graph (graphBallVertices g.graph o ell) M S):
    LabelledResamplingState.ProtectedPatches
      (g.admissibleState (graphBallVertices g.graph o ell) boundary S) selector R:=by
  let T:=graphBallVertices g.graph o ell
  let s:=g.admissibleState T boundary S
  have hempty:=allLargeSampleGood_rejected_empty g.graph o ell selector R M hmargin hsel hTree S hS
  apply LabelledResamplingState.protectedPatches_of_allLargeSampleGood s selector R M hM hS
  intro i
  have hacc:boundary i∈acceptedResamplingIndices g.graph T selector S:=by
    by_contra hn
    have hh:boundary i∈rejectedResamplingIndices g.graph T selector S:=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hn⟩
    rw [hempty] at hh
    exact Finset.not_mem_empty _ hh
  exact (Finset.mem_filter.mp hacc).2

/-- M=2R_aux protects radius-R_work balls by a factor at least eight.
The sampling selector remains the original work selector R_work/4. -/
theorem eventually_source_protectedPatches (a d:ℕ)(cAux:ℝ)
    (ha:0<a)(hd:3≤d)(hc:0<cAux):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      let ell:=actualCavityDepth a d N z-1
      let R:=logarithmicRadius (cAux/16) d N
      let M:=2*logarithmicRadius (cAux/4) d N
      (graphBall g.graph o R).IsTree→∀{ι:Type*}[Fintype ι]
      (boundary:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
      (S:LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)),
      AllLargeSampleGood g.graph (graphBallVertices g.graph o ell) M S→
      LabelledResamplingState.ProtectedPatches
        (g.admissibleState (graphBallVertices g.graph o ell) boundary S) (R/4) R:=by
  have hdepth:=(lowerLogLogRadius_tendsto a d ha hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [hdepth,eventually_resampling_radius_margin a d 2 2 (cAux/16) hd (by positivity),
    Filter.eventually_ge_atTop 1] with N hdepth hmargin hN
  intro g o z
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let R:=logarithmicRadius (cAux/16) d N
  let M:=2*logarithmicRadius (cAux/4) d N
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepth).2
  have h4:4*R≤logarithmicRadius (cAux/4) d N:=by
    have hh:=logarithmicRadius_nat_mul_lower 4 d N (cAux/16) hd hN (by positivity)
    rw [show ((4:ℕ):ℝ)*(cAux/16)=cAux/4 by norm_num;ring] at hh
    exact hh
  have hR:2≤R:=by dsimp only [R];omega
  have hM:4*R+3≤M:=by dsimp only [M];omega
  intro hTree ι _ boundary S hS
  exact protectedPatches_of_source_tree g o ell (R/4) R M (by omega) hM (by omega) hTree boundary S hS

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_source_protectedPatches
