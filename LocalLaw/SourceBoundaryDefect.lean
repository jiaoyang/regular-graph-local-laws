import LocalLaw.SourceSurgeryGoodLabels
import LocalLaw.SourceEndpointMatrices
import LocalLaw.EndpointPostCross
import LocalLaw.BoundaryDefectAggregation

/-! # The genuine boundary defect and its sparse off-diagonal aggregation -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceBoundaryDefectDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

def sourceBoundaryDefect (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (q z : ℂ) : Matrix ι ι ℂ :=
  (g.sourceEndpointT T labels S selector z-g.sourceEndpointQ T labels S selector r q z).submatrix
    ((g.admissibleState T labels S).endpointFinalBoundaryRoot selector)
    ((g.admissibleState T labels S).endpointFinalBoundaryRoot selector)

theorem sourceBoundaryDefect_isSymm (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (q z : ℂ) : (g.sourceBoundaryDefect T labels S selector r q z).IsSymm := by
  let s := g.admissibleState T labels S
  let F := g.labelledResampledGraph T labels S selector
  have hphys : ((F.deficient.delete T).G z).IsSymm := by
    have h := (F.deficient.delete T).extensionGreen_isSymm (0:ℂ) z
    simpa only [DeficientGraph.extensionGreen,DeficientGraph.H,boundaryGreen,boundaryMatrix,
      zero_smul,sub_zero,green,DeficientGraph.G] using h
  have hmodel := (g.switchedEndpointModel T labels S selector r).extensionGreen_isSymm q z
  ext u v
  change (F.deficient.delete T).G z _ _ -
      (g.switchedEndpointModel T labels S selector r).extensionGreen q z _ _ =
    (F.deficient.delete T).G z _ _ -
      (g.switchedEndpointModel T labels S selector r).extensionGreen q z _ _
  rw [hphys.apply,hmodel.apply]

def sourceSurgeryGoodIndices (g : RegularGraph N d) (o : Fin N) (ell R : ℕ)
    (hfit : ell+1≤R/8) (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (z : ℂ) (φ : ℝ) (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) : Finset ι :=
  Finset.univ.filter (fun i => labels i ∈ g.sourceSurgeryGoodLabels o ell R hfit z φ S)

/-- Actual paired bounds on accepted good tips imply a two-sided good-label
pattern on the literal boundary defect. The transpose case is derived from
physical/model symmetry. -/
theorem sourceBoundaryDefect_sparse_pattern (g : RegularGraph N d) (o : Fin N)
    (ell R r : ℕ) (hfit : ell+1≤R/8)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (q z : ℂ) (φ γ : ℝ)
    (hpaired : ∀ (i : (g.admissibleState (graphBallVertices g.graph o ell) labels S).AdmissibleSampleIndex (R/4))
      (j : ι), j≠i.val → labels i.val ∉ multiattachmentBoundaryLabels g.graph o hfit →
      labels i.val ∈ g.sourceCorrelationGoodLabels (graphBallVertices g.graph o ell) z φ (R/4) S →
      let T := graphBallVertices g.graph o ell
      let s := g.admissibleState T labels S
      ‖(g.sourceEndpointT T labels S (R/4) z-g.sourceEndpointQ T labels S (R/4) r q z)
        (s.endpointRootLabel (R/4) (Sum.inr (i,1))) (s.endpointFinalBoundaryRoot (R/4) j)‖≤γ) :
    let good := g.sourceSurgeryGoodIndices o ell R hfit labels z φ S
    ∀ u v, u≠v → (u∈good ∨ v∈good) →
      ‖g.sourceBoundaryDefect (graphBallVertices g.graph o ell) labels S (R/4) r q z u v‖≤γ := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T labels S
  have hone (u v : ι) (hu : u ∈ g.sourceSurgeryGoodIndices o ell R hfit labels z φ S) (huv : u≠v) :
      ‖g.sourceBoundaryDefect T labels S (R/4) r q z u v‖≤γ := by
    have hgood := (Finset.mem_filter.mp hu).2
    have hp := g.sourceSurgeryGoodLabels_properties o ell R hfit z φ S (labels u) hgood
    have helig : s.Eligible (R/4) u := (Finset.mem_filter.mp hp.2.2).2
    let i : s.AdmissibleSampleIndex (R/4) := ⟨u,helig⟩
    have h := hpaired i v (Ne.symm huv) hp.2.1 hp.1
    change ‖(g.sourceEndpointT T labels S (R/4) z-g.sourceEndpointQ T labels S (R/4) r q z)
      (s.endpointFinalBoundaryRoot (R/4) u) (s.endpointFinalBoundaryRoot (R/4) v)‖≤γ
    simpa only [LabelledResamplingState.endpointFinalBoundaryRoot,dif_pos helig] using h
  intro u v huv hg
  rcases hg with hu | hv
  · exact hone u v hu huv
  · rw [(g.sourceBoundaryDefect_isSymm T labels S (R/4) r q z).apply]
    exact hone v u hv (Ne.symm huv)

end RegularGraph
end LocalLaw
