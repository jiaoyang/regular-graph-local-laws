import LocalLaw.ActualEndpointComparisonSupport
import LocalLaw.EndpointOldModelRows

/-!
# The actual good-label off-diagonal surgery estimate

Physical and model inverse updates, the coupling mass, both comparison
supports, old model cross zeros and old correlation bounds are derived from
actual resampling. The remaining old approximation and post-model row caps
are precisely the independently supplied endpoint stability inputs.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance actualPairedEndpointSurgeryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem actual_paired_endpoint_offdiagonal (g : RegularGraph N d) (hd : 3≤d) (o : Fin N)
    (ell selector r R radius : ℕ) (hsep : 2*r+2≤selector) (hmargin : ell+r+1≤R)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (i : (g.admissibleState (graphBallVertices g.graph o ell) labels S).AdmissibleSampleIndex selector)
    (hnot : labels i.val ∉ multiattachmentBoundaryLabels g.graph o (by omega : ell+1≤R))
    (j : ι) (hji : j≠i.val) (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im)
    (C δ φ : ℝ) (hC : 0≤C) (hδ : 0≤δ) (hφ : 0≤φ)
    (hgood : labels i.val ∈ g.sourceCorrelationGoodLabels (graphBallVertices g.graph o ell) z φ radius S)
    (hQrow : ∀ u, ∑ v, ‖g.sourceEndpointQ (graphBallVertices g.graph o ell) labels S selector r q z u v‖ ≤ C)
    (hQcol : ∀ v, ∑ u, ‖g.sourceEndpointQ (graphBallVertices g.graph o ell) labels S selector r q z u v‖ ≤ C)
    (hE : ∀ u v, ‖(g.sourceEndpointR (graphBallVertices g.graph o ell) labels S selector z -
      g.sourceEndpointP (graphBallVertices g.graph o ell) labels S selector r q z) u v‖ ≤ δ)
    (hsmall : (Fintype.card ((g.admissibleState (graphBallVertices g.graph o ell) labels S).endpointModelRoots selector) : ℝ) *
      (1+C*(2*(d:ℝ)/Real.sqrt ((d:ℝ)-1))) * (2*(d:ℝ)/Real.sqrt ((d:ℝ)-1))*δ ≤ 1/2) :
    let T := graphBallVertices g.graph o ell
    let s := g.admissibleState T labels S
    let tip := s.endpointRootLabel selector (Sum.inr (i,1))
    let target := s.endpointFinalBoundaryRoot selector j
    let w := 2*(d:ℝ)/Real.sqrt ((d:ℝ)-1)
    ‖(g.sourceEndpointT T labels S selector z - g.sourceEndpointQ T labels S selector r q z) tip target‖ ≤
      (1+C*w)^2*φ+2*(1+C*w)^3*(2*δ+(Fintype.card (s.endpointModelRoots selector):ℝ)*φ)*w*δ := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T labels S
  let w := 2*(d:ℝ)/Real.sqrt ((d:ℝ)-1)
  have hupdates := g.source_endpoint_updates hd T labels S selector r q z hz hq
  have hW := g.source_endpoint_coupling_mass T labels S selector
  have hs := g.source_endpoint_comparison_support hd o ell selector r R hsep hmargin labels S i hnot j hji q z hz hq
  apply surgery_off_diagonal_of_isolated_pair
    (g.sourceEndpointR T labels S selector z) (g.sourceEndpointT T labels S selector z)
    (g.sourceEndpointP T labels S selector r q z) (g.sourceEndpointQ T labels S selector r q z)
    (g.sourceEndpointW T labels S selector) hupdates.1 hupdates.2.2.2 C w δ φ hC (by dsimp only [w]; positivity)
      hδ hφ hQrow hQcol hW.1 hW.2 hE hsmall
      (s.endpointRootLabel selector (Sum.inr (i,1))) (s.endpointFinalBoundaryRoot selector j)
      (s.endpointPairFinset selector i) (s.endpointPairFinset_card selector i) hs.1 hs.2
  · intro k hk l hl
    exact g.endpointModel_pair_zero_outside hd T labels S selector r hsep i q z hz hq k hk l hl
  · intro k hk l hl
    exact g.source_good_endpoint_pair_row T labels S selector radius z φ i hgood k l hk hl

end RegularGraph
end LocalLaw
