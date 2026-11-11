import LocalLaw.FilledBoundarySchur
import LocalLaw.NestedIsolatedModel
import LocalLaw.OldEndpointComponentCounts
import LocalLaw.ActualEndpointAttachments

/-!
# The old retained reference is independent of the random samples

The sampled pair patches are isolated from the central exterior patch in the
old model. Its genuine boundary block, and hence its filled retained Green
function, are exactly those of the fixed expanded root ball.
-/

noncomputable section
namespace LocalLaw
local instance centralReferenceIndependenceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Filling the complete outside boundary neighborhood recovers an ordinary
expanded root ball, with the extra boundary step counted exactly. -/
theorem filled_centralBoundary_eq_ball {V : Type*} (G : SimpleGraph V) (o : V) (ell r : ℕ) :
    filledExteriorVertices (graphBallVertices G o ell)
      (centralBoundaryVertices G (graphBallVertices G o ell) r) =
        graphBallVertices G o (ell + r + 1) := by
  let T := graphBallVertices G o ell
  apply Set.Subset.antisymm
  · rintro v (hv | ⟨x, hx, rfl⟩)
    · exact graphBallVertices_mono G o (by omega) hv
    · exact centralBoundaryVertices_subset_original_ball G o ell r (ell + r + 1) le_rfl x hx
  · intro v hv
    by_cases hvt : v ∈ T
    · exact Or.inl hvt
    · have hv' : v ∈ graphBallVertices G o (ell + (r + 1)) := by
        simpa only [Nat.add_assoc] using hv
      obtain ⟨e, q, hq⟩ := expanded_root_ball_outside_tail G o v ell (r + 1) hvt hv'
      apply Or.inr
      refine ⟨⟨v, hvt⟩, ?_, rfl⟩
      exact ⟨boundaryOuterEndpoint G T e, ⟨e, rfl⟩,
        (SimpleGraph.edist_le q).trans (ENat.coe_le_coe.mpr (by omega : q.length ≤ r))⟩

namespace RegularGraph
variable {N d : ℕ} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem endpointModel_boundary_eq_central (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (boundary : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (a b : BoundaryOrientedEdge g.graph T) :
    let s := g.admissibleState T boundary samples
    let e := s.endpointModelKernelEmbedding selector r
    (g.endpointModel T boundary samples selector r).extensionGreen q z
      (e ⟨boundaryOutsideVertex g.graph T a, Or.inl ⟨a, rfl⟩⟩)
      (e ⟨boundaryOutsideVertex g.graph T b, Or.inl ⟨b, rfl⟩⟩) =
      ((g.deficient.delete T).restrict (centralBoundaryVertices g.graph T r)).extensionGreen q z
        (centralBoundaryCenter g.graph T r a) (centralBoundaryCenter g.graph T r b) := by
  let s := g.admissibleState T boundary samples
  exact (g.deficient.delete T).nested_isolated_extensionGreen hd
    (s.endpointModelVertices selector r) (s.centralEndpointPatch r)
    (s.centralEndpointPatch_subset_model selector r)
    (fun x hx y hy hyn => s.endpointModel_central_closed selector r hsep
      x (s.centralEndpointPatch_subset_model selector r hx) hx y hy hyn)
    q z hz hq (centralBoundaryCenter g.graph T r a) (centralBoundaryCenter g.graph T r b)

omit [Fintype ι] in
/-- The old common filled reference kernel is precisely the deterministic
central reference. No averaging over its random auxiliary patches occurs. -/
theorem filledEndpointReference_eq_central (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (boundary : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    g.filledRetainedGreen T ((g.admissibleState T boundary samples).endpointModelVertices selector r) q z =
      g.filledRetainedGreen T (centralBoundaryVertices g.graph T r) q z := by
  let s := g.admissibleState T boundary samples
  have hbig : ∀ a : BoundaryOrientedEdge g.graph T, boundaryOutsideVertex g.graph T a ∈
      s.endpointModelVertices selector r := fun a => ⟨boundaryOutsideVertex g.graph T a, Or.inl ⟨a, rfl⟩,
        center_mem_graphBall (outsideGraph g.graph T) (boundaryOutsideVertex g.graph T a) r⟩
  have hsmall : ∀ a : BoundaryOrientedEdge g.graph T, boundaryOutsideVertex g.graph T a ∈
      centralBoundaryVertices g.graph T r := fun a => (centralBoundaryCenter g.graph T r a).property
  apply g.filledRetainedGreen_eq_of_boundary_block g hd T _ _ hbig hsmall (Equiv.refl _) (fun _ => rfl)
    rfl q z hz hq
  exact g.endpointModel_boundary_eq_central hd T boundary samples selector r hsep q z hz hq

end RegularGraph
end LocalLaw
