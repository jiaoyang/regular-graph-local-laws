import SpectralConsequences.CavityVertexMean

/-! # Actual conditional drift of the center cavity average -/
open scoped BigOperators
open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceCavitySiteDriftDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_cavity_site_drift (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32) (hB:0≤B):
    ∀ᶠ N:ℕ in atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree→
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      let selector:=logarithmicRadius (c/4) d N/4
      ∀{ι:Type}[Fintype ι](labels:ι≃BoundaryOrientedEdge g.graph T),
      ‖finiteComplexMean (fun samples:LocalSamplingFiber g.graph T=>
        cavityAtVertex (g.labelledResampledGraph T labels samples selector).graph d z o)-
        cavityIterate z (g.Q z) (ell+1)-trivialCavityCorrection N d ell z‖≤
        sourceCavityDriftError g a β B labels selector (logarithmicRadius β d N) ell z:=by
  filter_upwards [eventually_source_cavity_physical_drift a b d c β B ha hb hd hc hβ hβc hB]
    with N hdrift
  intro g o z hz hfloor hzB badCount hold htree
  dsimp only
  intro ι _ labels
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  obtain ⟨hell,hminor⟩:=hdrift g o z hz hfloor hzB badCount hold htree
  have hell1:1≤ell:=by omega
  let J:=g.graph.neighborSet o
  have hcard:0<Fintype.card J:=by
    change 0<Fintype.card (g.graph.neighborSet o)
    rw [SimpleGraph.card_neighborSet_eq_degree,g.regular o]
    omega
  letI:Nonempty J:=Fintype.card_pos_iff.mp hcard
  let f:LocalSamplingFiber g.graph T→J→ℂ:=fun S j=>
    let jt:=rootNeighborInBall g.graph o ell hell1 j
    (g.labelledResampledGraph T labels S selector).retainedPhysicalMinor T jt z
      (g.truncatedCavityRoot o ell jt j.property.symm) (g.truncatedCavityRoot o ell jt j.property.symm)
  have hpoint (S:LocalSamplingFiber g.graph T):
      cavityAtVertex (g.labelledResampledGraph T labels S selector).graph d z o=
        finiteComplexMean (f S):=
    resampled_cavityAtVertex_eq_neighbor_mean g o ell hell1 labels S selector z
  have hnorm:=finiteComplexMean_norm_bound (fun j:J=>finiteComplexMean (fun S=>f S j)-
    cavityIterate z (g.Q z) (ell+1)-trivialCavityCorrection N d ell z)
    (sourceCavityDriftError g a β B labels selector (logarithmicRadius β d N) ell z)
    (fun j=>hminor (rootNeighborInBall g.graph o ell hell1 j) j.property.symm labels)
  have hmean:finiteComplexMean (fun S:LocalSamplingFiber g.graph T=>
      cavityAtVertex (g.labelledResampledGraph T labels S selector).graph d z o)=
      finiteComplexMean (fun j:J=>finiteComplexMean (fun S=>f S j)):=by
    simp_rw [hpoint]
    exact finiteComplexMean_comm f
  rw [hmean]
  simpa only [finiteComplexMean_sub,finiteComplexMean_const] using hnorm

end RegularGraph
end SpectralConsequences
