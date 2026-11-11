import LocalLaw.CentralEndpointCharges
import LocalLaw.EndpointBranchTrees
import LocalLaw.EndpointComponentCounts

/-! # The J-test isolates an accepted root's central component

The accepted a-root is farther than the selector from every other boundary
label's root. At the smaller model radius its actual central component
therefore has exactly its own boundary label.
-/

noncomputable section
namespace LocalLaw
local instance eligibleCentralIsolationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type*} {T : Set V} {ι : Type*}

theorem eligible_boundary_root_far (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i : s.AdmissibleSampleIndex selector) (β : BoundaryOrientedEdge s.graph T)
    (hβ : β ≠ s.boundary i.val) :
    (selector : ℕ∞) < (outsideGraph s.graph T).edist
      (boundaryOuterEndpoint s.graph T (s.boundary i.val)) (boundaryOuterEndpoint s.graph T β) :=
  i.property.2 β hβ _ ((outsideTriple_mem_iff s.graph T s.samples _ _).mpr (Or.inl rfl))
    _ ((outsideTriple_mem_iff s.graph T s.samples _ _).mpr (Or.inl rfl))

theorem eligible_central_reachable_boundary_unique (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (hsep : 2 * r + 1 ≤ selector) (i : s.AdmissibleSampleIndex selector)
    (β : BoundaryOrientedEdge s.graph T)
    (hreach : (centralBoundaryGraph s.graph T r).Reachable
      (centralBoundaryCenter s.graph T r (s.boundary i.val)) (centralBoundaryCenter s.graph T r β)) :
    β = s.boundary i.val := by
  let H := outsideGraph s.graph T
  let a := boundaryOuterEndpoint s.graph T (s.boundary i.val)
  let K := centralBoundaryGraph s.graph T r
  let A : Set (centralBoundaryVertices s.graph T r) := {v | H.edist a v.val ≤ (r : ℕ∞)}
  have hcut : ∀ x ∈ A, ∀ y ∉ A, ¬K.Adj x y := by
    intro x hx y hy hxy
    obtain ⟨u, ⟨γ, rfl⟩, hγ⟩ := y.property
    by_cases hγi : γ = s.boundary i.val
    · exact hy (by simpa only [hγi] using hγ)
    · exact graphBalls_no_edge_of_edist_gt H a (boundaryOuterEndpoint s.graph T γ) r
        ((ENat.coe_le_coe.mpr hsep).trans_lt (s.eligible_boundary_root_far selector i γ hγi))
        x.val hx y.val hγ hxy
  obtain ⟨p⟩ := hreach
  have hstart : centralBoundaryCenter s.graph T r (s.boundary i.val) ∈ A := by
    change H.edist a a ≤ (r : ℕ∞)
    simp
  have hend := walk_end_mem_isolated K A hcut p hstart
  by_contra hβ
  have hfar := s.eligible_boundary_root_far selector i β hβ
  exact not_lt_of_ge ((show H.edist a (boundaryOuterEndpoint s.graph T β) ≤ (r : ℕ∞) from hend).trans
    (ENat.coe_le_coe.mpr (by omega : r ≤ selector))) hfar

theorem eligible_central_boundary_fiber_card_one (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (hsep : 2 * r + 1 ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    let c := (centralBoundaryGraph s.graph T r).connectedComponentMk
      (centralBoundaryCenter s.graph T r (s.boundary i.val))
    Nat.card (CentralBoundaryFiber s.graph T r c) = 1 := by
  dsimp only
  let c := (centralBoundaryGraph s.graph T r).connectedComponentMk
    (centralBoundaryCenter s.graph T r (s.boundary i.val))
  let canonical : CentralBoundaryFiber s.graph T r c := ⟨s.boundary i.val, rfl⟩
  letI : Unique (CentralBoundaryFiber s.graph T r c) :=
    ⟨⟨canonical⟩, fun β => by
      apply Subtype.ext
      change β.val = s.boundary i.val
      exact s.eligible_central_reachable_boundary_unique selector r hsep i β.val
        (SimpleGraph.ConnectedComponent.exact β.property.symm)⟩
  exact Nat.card_unique

theorem endpoint_eligible_rootLabel_unique [Fintype ι] (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector) (i : s.AdmissibleSampleIndex selector)
    (β : BoundaryOrientedEdge s.graph T)
    (hlabel : (s.endpointBranchAttachmentData selector r hsep).rootLabel
      (s.endpointBoundaryRoot selector r) (s.endpointBoundaryRoot_mem_central selector r) β =
      (s.endpointBranchAttachmentData selector r hsep).centralLabel i) : β = s.boundary i.val := by
  let D := s.endpointBranchAttachmentData selector r hsep
  let e := s.endpointCentralIso selector r hsep
  have hr : ((s.endpointOldGraph selector r).induce D.core).Reachable
      (⟨D.attach i, D.attach_mem i⟩ : D.core)
      (⟨s.endpointBoundaryRoot selector r β, s.endpointBoundaryRoot_mem_central selector r β⟩ : D.core) :=
    SimpleGraph.ConnectedComponent.exact hlabel.symm
  exact s.eligible_central_reachable_boundary_unique selector r (by omega) i β (hr.map e.toHom)

end LabelledResamplingState
end LocalLaw
