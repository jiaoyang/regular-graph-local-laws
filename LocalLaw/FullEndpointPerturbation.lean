import LocalLaw.SourceEndpointPerturbation
import LocalLaw.RestrictedPerturbationIdentity
import LocalLaw.FilledExteriorModel
import LocalLaw.EndpointModelInvariance
import LocalLaw.SourceEndpointMatrices

/-! # Physical and model surgery on the complete modified vertex set

The finite endpoint set includes the retained vertices as well as the
accepted exterior endpoints. This supplies the actual full-graph update,
without a prior bound for any new physical Green entry.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance fullEndpointPerturbationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*}

theorem applySwitches_adj_of_away_support (L : List (SwitchingQuad V)) (G : SimpleGraph V)
    (x y : V) (hx : ∀ q ∈ L, x ∉ q.support) :
    (applySwitches L G).Adj x y ↔ G.Adj x y := by
  induction L generalizing G with
  | nil => rfl
  | cons q L ih =>
    rw [applySwitches_cons]
    have hnot : ¬q.footprint.Adj x y := fun h => hx q (by simp) (q.footprint_left_mem_support h)
    exact (ih (q.apply G) (fun p hp => hx p (by simp [hp]))).trans (q.adj_outside_footprint G hnot)

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*} [Fintype ι]

def fullResampleEndpoints (s : LabelledResamplingState V T ι) (selector : ℕ) : Set V :=
  {x | ∃ i, s.Eligible selector i ∧ x ∈ (s.quad i).support}

theorem fullResample_adj_of_away_endpoint (s : LabelledResamplingState V T ι)
    (selector : ℕ) (x y : V) (hx : x ∉ s.fullResampleEndpoints selector) :
    (s.fullResample selector).graph.Adj x y ↔ s.graph.Adj x y := by
  rw [s.fullResample_graph_eq_applySwitches selector]
  apply applySwitches_adj_of_away_support
  intro q hq hxq
  obtain ⟨i, _, hi, hqi⟩ := (s.mem_selectedQuads selector _ q).mp hq
  subst q
  exact hx ⟨i, hi, hxq⟩

theorem fullResample_adj_agrees_off_endpoints (s : LabelledResamplingState V T ι)
    (selector : ℕ) (x y : V)
    (haway : x ∉ s.fullResampleEndpoints selector ∨ y ∉ s.fullResampleEndpoints selector) :
    s.graph.Adj x y ↔ (s.fullResample selector).graph.Adj x y := by
  rcases haway with hx | hy
  · exact (s.fullResample_adj_of_away_endpoint selector x y hx).symm
  · rw [s.graph.adj_comm, (s.fullResample selector).graph.adj_comm]
    exact (s.fullResample_adj_of_away_endpoint selector y x hy).symm

variable [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem fullResample_difference_supported (s : LabelledResamplingState V T ι)
    (selector d : ℕ) (x y : V)
    (haway : x ∉ s.fullResampleEndpoints selector ∨ y ∉ s.fullResampleEndpoints selector) :
    (normalizedAdjacency (s.fullResample selector).graph d - normalizedAdjacency s.graph d) x y = 0 := by
  have hagree := s.fullResample_adj_agrees_off_endpoints selector x y haway
  simp only [Matrix.sub_apply, normalizedAdjacency, Matrix.smul_apply, smul_eq_mul,
    SimpleGraph.adjMatrix_apply]
  rw [hagree, sub_self]

theorem fullResample_endpoint_updates {I : Type*} [Fintype I]
    (s : LabelledResamplingState V T ι) (selector d : ℕ) (e : I ↪ V)
    (hcapture : s.fullResampleEndpoints selector ⊆ Set.range e) (z : ℂ) (hz : 0 < z.im) :
    let R := (green (normalizedAdjacency s.graph d) z).submatrix e e
    let U := (green (normalizedAdjacency (s.fullResample selector).graph d) z).submatrix e e
    let W := (normalizedAdjacency (s.fullResample selector).graph d - normalizedAdjacency s.graph d).submatrix e e
    (U + R * W * U = R) ∧ (U + U * W * R = R) := by
  apply green_embedded_finite_rank_updates _ _ (normalizedAdjacency_isHermitian _ _)
    (normalizedAdjacency_isHermitian _ _) e _ z hz
  intro x y hxy
  exact s.fullResample_difference_supported selector d x y
    (hxy.imp (fun hx hs => hx (hcapture hs)) (fun hy hs => hy (hcapture hs)))

theorem fullResample_endpoint_mass {I : Type*} [Fintype I]
    (s : LabelledResamplingState V T ι) (selector d : ℕ)
    (hdegree : ∀ v, s.graph.degree v ≤ d) (e : I ↪ V) :
    let W := (normalizedAdjacency (s.fullResample selector).graph d - normalizedAdjacency s.graph d).submatrix e e
    (∀ i, ∑ j, ‖W i j‖ ≤ 2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) ∧
      (∀ j, ∑ i, ‖W i j‖ ≤ 2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) := by
  have hnew : ∀ v, (s.fullResample selector).graph.degree v ≤ d := fun v =>
    (s.fullResample_degree selector v).le.trans (hdegree v)
  exact ⟨normalizedAdjacency_difference_endpoint_row_bound _ _ d hdegree hnew e,
    normalizedAdjacency_difference_endpoint_column_bound _ _ d hdegree hnew e⟩

def fullEndpointRoots (s : LabelledResamplingState V T ι) (selector : ℕ) : Set V :=
  filledExteriorVertices T (s.endpointModelRoots selector)

omit [Fintype ι] [Fintype V] [DecidableEq V] in
theorem fullResampleEndpoints_subset_fullEndpointRoots (s : LabelledResamplingState V T ι)
    (selector : ℕ) : s.fullResampleEndpoints selector ⊆ s.fullEndpointRoots selector := by
  rintro x ⟨i, hi, hx⟩
  change x = (s.quad i).a ∨ x ∈ (s.quad i).exterior at hx
  rcases hx with rfl | hx
  · left
    exact sampledSwitching_root_mem s.graph T s.samples (s.boundary i)
  · have hout : x ∉ T := fun ht =>
      Set.disjoint_left.mp (sampledSwitching_exterior_disjoint s.graph T s.samples (s.boundary i)) hx ht
    let v : (Tᶜ : Set V) := ⟨x, hout⟩
    right
    exact ⟨v, s.fullResampleOutsideEndpoints_subset_modelRoots selector ⟨i, hi, hx⟩, rfl⟩

def fullEndpointRootEmbedding (s : LabelledResamplingState V T ι) (selector : ℕ) :
    s.fullEndpointRoots selector ↪ V := ⟨Subtype.val, Subtype.val_injective⟩

def fullEndpointModelEmbedding (s : LabelledResamplingState V T ι) (selector r : ℕ) :
    s.fullEndpointRoots selector ↪ filledExteriorVertices T (s.endpointModelVertices selector r) where
  toFun x := ⟨x.val, by
    rcases x.property with hx | ⟨y, hy, heq⟩
    · exact Or.inl hx
    · exact Or.inr ⟨y, ⟨y, hy, by simp⟩, heq⟩⟩
  inj' x y h := by
    apply Subtype.ext
    exact congrArg (fun v : filledExteriorVertices T (s.endpointModelVertices selector r) => v.val) h

theorem fullEndpointRoot_physical_updates (s : LabelledResamplingState V T ι)
    (selector d : ℕ) (z : ℂ) (hz : 0 < z.im) :
    let e := s.fullEndpointRootEmbedding selector
    let R := (green (normalizedAdjacency s.graph d) z).submatrix e e
    let U := (green (normalizedAdjacency (s.fullResample selector).graph d) z).submatrix e e
    let W := (normalizedAdjacency (s.fullResample selector).graph d - normalizedAdjacency s.graph d).submatrix e e
    (U + R * W * U = R) ∧ (U + U * W * R = R) := by
  apply s.fullResample_endpoint_updates selector d (s.fullEndpointRootEmbedding selector) _ z hz
  intro x hx
  exact ⟨⟨x, s.fullResampleEndpoints_subset_fullEndpointRoots selector hx⟩, rfl⟩

end LabelledResamplingState

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem fullEndpoint_physical_model_updates (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (boundary : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector r : ℕ)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let s := g.admissibleState T boundary samples
    let gnew := g.labelledResampledGraph T boundary samples selector
    let S := filledExteriorVertices T (s.endpointModelVertices selector r)
    let e := s.fullEndpointModelEmbedding selector r
    let f := s.fullEndpointRootEmbedding selector
    let R := (g.G z).submatrix f f
    let U := (gnew.G z).submatrix f f
    let P := ((g.deficient.restrict S).extensionGreen q z).submatrix e e
    let Q := ((gnew.deficient.restrict S).extensionGreen q z).submatrix e e
    let W := (gnew.H - g.H).submatrix f f
    (U + R * W * U = R) ∧ (U + U * W * R = R) ∧
      (Q + P * W * Q = P) ∧ (Q + Q * W * P = P) := by
  let s := g.admissibleState T boundary samples
  let gnew := g.labelledResampledGraph T boundary samples selector
  let S := filledExteriorVertices T (s.endpointModelVertices selector r)
  let e := s.fullEndpointModelEmbedding selector r
  have hagree : ∀ x y, x ∉ Set.range (fun i => (e i).val) ∨ y ∉ Set.range (fun i => (e i).val) →
      (g.deficient.graph.Adj x y ↔ gnew.deficient.graph.Adj x y) := by
    intro x y hxy
    apply s.fullResample_adj_agrees_off_endpoints selector
    exact hxy.imp
      (fun hx hs => hx ⟨⟨x, s.fullResampleEndpoints_subset_fullEndpointRoots selector hs⟩, rfl⟩)
      (fun hy hs => hy ⟨⟨y, s.fullResampleEndpoints_subset_fullEndpointRoots selector hs⟩, rfl⟩)
  have hphysical := s.fullEndpointRoot_physical_updates selector d z hz
  have hmodel := g.deficient.restrict_endpoint_inverse_updates gnew.deficient hd S e
    (fun v => by simpa using g.regular v) (fun v => by simpa using gnew.regular v)
    hagree q z hz hq
  exact ⟨hphysical.1, hphysical.2, hmodel.1, hmodel.2⟩

end RegularGraph
end LocalLaw
