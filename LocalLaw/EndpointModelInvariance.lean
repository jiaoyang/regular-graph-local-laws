import LocalLaw.SourceEndpointPerturbation
import LocalLaw.AdmissibleEndpointPatches

/-!
# One genuine common endpoint-neighborhood vertex set

Every changed outside edge has both endpoints among the original endpoint
roots. The union of balls around that fixed root set is therefore exactly
unchanged by the actual labelled resampling. Old and new finite extension
models may use this same actual vertex set.
-/

noncomputable section
namespace LocalLaw
local instance endpointModelInvarianceDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type*} {T : Set V} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem fullResampleOutsideEndpoints_subset_modelRoots (s : LabelledResamplingState V T ι) (selector : ℕ) :
    s.fullResampleOutsideEndpoints selector ⊆ s.endpointModelRoots selector := by
  rintro x ⟨i, hi, hx⟩
  exact s.eligible_exterior_mem_endpointModelRoots selector i hi x hx

theorem endpointModelVertices_fullResample (s : LabelledResamplingState V T ι) (selector r : ℕ) :
    s.endpointModelVertices selector r =
      graphSetBall (outsideGraph (s.fullResample selector).graph T) (s.endpointModelRoots selector) r := by
  apply graphSetBall_eq_of_internal_changes
  intro x y hxy
  have hcapture := s.fullResampleOutsideEndpoints_subset_modelRoots selector
  rcases hxy with hx | hy
  · exact (s.fullResample_outside_adj_of_away_left selector x y (fun h => hx (hcapture h))).symm
  · rw [(outsideGraph s.graph T).adj_comm, (outsideGraph (s.fullResample selector).graph T).adj_comm]
    exact (s.fullResample_outside_adj_of_away_left selector y x (fun h => hy (hcapture h))).symm

def endpointModelRootEmbedding (s : LabelledResamplingState V T ι) (selector : ℕ) :
    s.endpointModelRoots selector ↪ (Tᶜ : Set V) := ⟨Subtype.val, Subtype.val_injective⟩

variable [Fintype V] [DecidableEq V]

/-- Genuine physical old/new endpoint equations on the actual source root
set; the support condition is proved from the selected switchings. -/
theorem endpointModelRoot_physical_updates (s : LabelledResamplingState V T ι)
    (selector d : ℕ) (z : ℂ) (hz : 0 < z.im) :
    let e := s.endpointModelRootEmbedding selector
    let H := normalizedAdjacency (outsideGraph s.graph T) d
    let K := normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d
    let R := (green H z).submatrix e e
    let U := (green K z).submatrix e e
    let W := (K - H).submatrix e e
    (U + R * W * U = R) ∧ (U + U * W * R = R) := by
  apply s.fullResample_outside_endpoint_updates selector d (s.endpointModelRootEmbedding selector) _ z hz
  intro x hx
  exact ⟨⟨x, s.fullResampleOutsideEndpoints_subset_modelRoots selector hx⟩, rfl⟩

theorem endpointModelRoot_physical_mass (s : LabelledResamplingState V T ι)
    (selector d : ℕ) (hdegree : ∀ v, s.graph.degree v ≤ d) :
    let e := s.endpointModelRootEmbedding selector
    let W := (normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d -
      normalizedAdjacency (outsideGraph s.graph T) d).submatrix e e
    (∀ i, ∑ j, ‖W i j‖ ≤ 2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) ∧
      (∀ j, ∑ i, ‖W i j‖ ≤ 2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) :=
  s.fullResample_outside_endpoint_mass selector d hdegree (s.endpointModelRootEmbedding selector)

end LabelledResamplingState
end LocalLaw
