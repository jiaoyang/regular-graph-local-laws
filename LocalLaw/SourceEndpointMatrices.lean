import LocalLaw.EndpointModelDiameter
import LocalLaw.DetachedEndpointModel
import LocalLaw.RestrictedPerturbationIdentity

/-!
# Canonical actual source endpoint matrices

All five matrices use the same deduplicated actual endpoint roots. The
physical and finite-model inverse updates share exactly the same physical
coupling. Saturation and support prove this equality without a separation
or reference-budget hypothesis.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceEndpointMatricesDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

def sourceEndpointR (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (z : ℂ) :=
  ((g.deficient.delete T).G z).submatrix
    ((g.admissibleState T boundary samples).endpointModelRootEmbedding selector)
    ((g.admissibleState T boundary samples).endpointModelRootEmbedding selector)

def sourceEndpointT (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (z : ℂ) :=
  (((g.labelledResampledGraph T boundary samples selector).deficient.delete T).G z).submatrix
    ((g.admissibleState T boundary samples).endpointModelRootEmbedding selector)
    ((g.admissibleState T boundary samples).endpointModelRootEmbedding selector)

def sourceEndpointP (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (q z : ℂ) :=
  ((g.endpointModel T boundary samples selector r).extensionGreen q z).submatrix
    ((g.admissibleState T boundary samples).endpointModelKernelEmbedding selector r)
    ((g.admissibleState T boundary samples).endpointModelKernelEmbedding selector r)

def sourceEndpointQ (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (q z : ℂ) :=
  ((g.switchedEndpointModel T boundary samples selector r).extensionGreen q z).submatrix
    ((g.admissibleState T boundary samples).endpointModelKernelEmbedding selector r)
    ((g.admissibleState T boundary samples).endpointModelKernelEmbedding selector r)

def sourceEndpointW (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) :=
  (((g.labelledResampledGraph T boundary samples selector).deficient.delete T).H -
      (g.deficient.delete T).H).submatrix
    ((g.admissibleState T boundary samples).endpointModelRootEmbedding selector)
    ((g.admissibleState T boundary samples).endpointModelRootEmbedding selector)

/-- Genuine physical and model updates on the same actual endpoint type,
in both orientations. No selector separation is needed. -/
theorem source_endpoint_updates (g : RegularGraph N d) (hd : 3 ≤ d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let R := g.sourceEndpointR T boundary samples selector z
    let U := g.sourceEndpointT T boundary samples selector z
    let P := g.sourceEndpointP T boundary samples selector r q z
    let Q := g.sourceEndpointQ T boundary samples selector r q z
    let W := g.sourceEndpointW T boundary samples selector
    (U + R * W * U = R) ∧ (U + U * W * R = R) ∧
      (Q + P * W * Q = P) ∧ (Q + Q * W * P = P) := by
  let s := g.admissibleState T boundary samples
  let S := s.endpointModelVertices selector r
  let e := s.endpointModelKernelEmbedding selector r
  let old := g.deficient.delete T
  let new := (g.labelledResampledGraph T boundary samples selector).deficient.delete T
  have hgraph : ∀ x y, x ∉ Set.range (fun i => (e i).val) ∨ y ∉ Set.range (fun i => (e i).val) →
      (old.graph.Adj x y ↔ new.graph.Adj x y) := by
    intro x y hxy
    have haway : x ∉ s.fullResampleOutsideEndpoints selector ∨ y ∉ s.fullResampleOutsideEndpoints selector :=
      hxy.imp
        (fun hx hs => hx ⟨⟨x, s.fullResampleOutsideEndpoints_subset_modelRoots selector hs⟩, rfl⟩)
        (fun hy hs => hy ⟨⟨y, s.fullResampleOutsideEndpoints_subset_modelRoots selector hs⟩, rfl⟩)
    rcases haway with hx | hy
    · exact (s.fullResample_outside_adj_of_away_left selector x y hx).symm
    · rw [old.graph.adj_comm, new.graph.adj_comm]
      exact (s.fullResample_outside_adj_of_away_left selector y x hy).symm
  have hphysical := s.endpointModelRoot_physical_updates selector d z hz
  have hmodel := old.restrict_endpoint_inverse_updates new hd S e
    (g.deleted_degree_deficit_saturated T)
    ((g.labelledResampledGraph T boundary samples selector).deleted_degree_deficit_saturated T)
    hgraph q z hz hq
  exact ⟨hphysical.1, hphysical.2, hmodel.1, hmodel.2⟩

theorem source_endpoint_coupling_mass (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) :
    let W := g.sourceEndpointW T boundary samples selector
    (∀ i, ∑ j, ‖W i j‖ ≤ 2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) ∧
      (∀ j, ∑ i, ‖W i j‖ ≤ 2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) :=
  (g.admissibleState T boundary samples).endpointModelRoot_physical_mass selector d (fun v => (g.regular v).le)

end RegularGraph
end LocalLaw
