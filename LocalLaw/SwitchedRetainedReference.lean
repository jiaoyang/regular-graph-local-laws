import LocalLaw.BoundaryBlockPreservation
import LocalLaw.CentralReferenceIndependence
import LocalLaw.FilledRetainedExpansion

/-!
# The switched retained reference equals a fixed old reference exactly

Actual boundary blocks are preserved after relabelling, the inner adjacency
is unchanged, and every boundary incidence is captured. The new filled
model therefore has precisely the old expanded-ball retained Green matrix.
Its weights are independent of all sampled edges.
-/

noncomputable section
namespace LocalLaw
local instance switchedRetainedReferenceDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type} [Fintype ι]

theorem fullResample_boundary_inner_endpoint (s : LabelledResamplingState V T ι)
    (selector : ℕ) (j : ι) :
    ((s.fullResample selector).boundary j).val.1 = (s.boundary j).val.1 := by
  have hh := congrArg SwitchingQuad.a (s.fullResample_quad_at_label selector j)
  simpa only [apply_ite, quad, sampledSwitchingQuad, SwitchingQuad.inverse, ite_self] using hh

theorem endpointModel_contains_new_boundary (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (a : BoundaryOrientedEdge (s.fullResample selector).graph T) :
    boundaryOutsideVertex (s.fullResample selector).graph T a ∈ s.endpointModelVertices selector r := by
  obtain ⟨j, rfl⟩ := (s.fullResample selector).boundary.surjective a
  rw [← s.endpointFinalBoundaryRoot_outer selector j]
  exact ⟨(s.endpointFinalBoundaryRoot selector j).val,
    (s.endpointFinalBoundaryRoot selector j).property,
    center_mem_graphBall (outsideGraph s.graph T) _ r⟩

end LabelledResamplingState
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

/-- An exact sample-independent retained reference, obtained without any
finite-class premise, approximation, or probabilistic good event. -/
theorem switched_filled_reference_eq_old_central (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (boundary : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) (hr : r + 2 ≤ selector)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let s := g.admissibleState T boundary samples
    let gnew := g.labelledResampledGraph T boundary samples selector
    gnew.filledRetainedGreen T (s.endpointModelVertices selector r) q z =
      g.filledRetainedGreen T (centralBoundaryVertices g.graph T r) q z := by
  dsimp only
  let s := g.admissibleState T boundary samples
  let gnew := g.labelledResampledGraph T boundary samples selector
  let K := s.endpointModelVertices selector r
  have hK : ∀ a : BoundaryOrientedEdge g.graph T, boundaryOutsideVertex g.graph T a ∈ K :=
    fun a => ⟨_, Or.inl ⟨a, rfl⟩, center_mem_graphBall (outsideGraph g.graph T) _ r⟩
  have hKnew : ∀ a : BoundaryOrientedEdge gnew.graph T, boundaryOutsideVertex gnew.graph T a ∈ K :=
    s.endpointModel_contains_new_boundary selector r
  let changeBoundary : BoundaryOrientedEdge g.graph T ≃ BoundaryOrientedEdge gnew.graph T :=
    boundary.symm.trans (s.fullResample selector).boundary
  have hfirst : ∀ a, (changeBoundary a).val.1 = a.val.1 := by
    intro a
    exact (s.fullResample_boundary_inner_endpoint selector (boundary.symm a)).trans
      (congrArg (fun e : BoundaryOrientedEdge g.graph T => e.val.1) (boundary.apply_symm_apply a))
  have hinner : g.H.submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N) =
      gnew.H.submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N) := by
    change (normalizedAdjacency g.graph d).submatrix _ _ = (normalizedAdjacency gnew.graph d).submatrix _ _
    rw [← normalizedAdjacency_induce, ← normalizedAdjacency_induce]
    exact congrArg (fun G => normalizedAdjacency G d) (s.fullResample_induce selector).symm
  have hfilled := g.filledRetainedGreen_eq_of_boundary_block gnew hd T K K hK hKnew
    changeBoundary hfirst hinner q z hz hq
  have hblock : ∀ a b,
      ((g.deficient.delete T).restrict K).extensionGreen q z
        (g.filledBoundaryVertex T K hK a) (g.filledBoundaryVertex T K hK b) =
      ((gnew.deficient.delete T).restrict K).extensionGreen q z
        (gnew.filledBoundaryVertex T K hKnew (changeBoundary a))
        (gnew.filledBoundaryVertex T K hKnew (changeBoundary b)) := by
    intro a b
    obtain ⟨j, rfl⟩ := boundary.surjective a
    obtain ⟨k, rfl⟩ := boundary.surjective b
    have hh := (g.sourceEndpoint_boundary_block_preserved hd T boundary samples selector r hsep hr q z hz hq j k).symm
    have hnew (i : ι) : gnew.filledBoundaryVertex T K hKnew ((s.fullResample selector).boundary i) =
        s.endpointModelKernelEmbedding selector r (s.endpointFinalBoundaryRoot selector i) := by
      apply Subtype.ext
      exact (s.endpointFinalBoundaryRoot_outer selector i).symm
    simp only [changeBoundary, Equiv.trans_apply, Equiv.symm_apply_apply]
    calc
      _ = g.sourceEndpointP T boundary samples selector r q z
          (s.endpointRootLabel selector (Sum.inl (boundary j)))
          (s.endpointRootLabel selector (Sum.inl (boundary k))) := rfl
      _ = g.sourceEndpointQ T boundary samples selector r q z
          (s.endpointFinalBoundaryRoot selector j) (s.endpointFinalBoundaryRoot selector k) := hh
      _ = _ := congrArg₂ (((gnew.deficient.delete T).restrict K).extensionGreen q z)
        (hnew j).symm (hnew k).symm
  exact (hfilled hblock).symm.trans
    (g.filledEndpointReference_eq_central hd T boundary samples selector r hsep q z hz hq)

end RegularGraph
end LocalLaw
