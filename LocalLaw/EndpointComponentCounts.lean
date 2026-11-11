import LocalLaw.EndpointBranchTrees
import LocalLaw.CentralEndpointCharges

/-! # Actual endpoint-root counts in switched components

Boundary labels are counted with multiplicity first. The actual finite root
set is a surjective image of those labels and the selected two endpoints,
so its component cardinality has the same uniform bound.
-/

noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance endpointComponentCountsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance centralBoundaryFiberFinite {V : Type*} [Fintype V] (G : SimpleGraph V)
    (T : Set V) (r : ℕ) (c : (centralBoundaryGraph G T r).ConnectedComponent) :
    Finite (CentralBoundaryFiber G T r c) := by
  unfold CentralBoundaryFiber
  infer_instance

theorem central_boundary_fiber_card_bound_of_set_eq {V : Type*} [Fintype V]
    (G : SimpleGraph V) (T : Set V) (o : V) (ell r R ω : ℕ)
    (hT : T = graphBallVertices G o ell) (hmargin : ell + r + 1 ≤ R)
    (hbudget : graphBallExcess G o R ≤ ω) (c : (centralBoundaryGraph G T r).ConnectedComponent) :
    Nat.card (CentralBoundaryFiber G T r c) ≤ ω + 1 := by
  subst T
  exact central_boundary_fiber_card_bound G o ell r R ω hmargin hbudget c

namespace LabelledResamplingState
variable {V : Type*} {T : Set V} {ι : Type*} [Fintype ι]

def endpointBoundaryRoot (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (α : BoundaryOrientedEdge s.graph T) : s.endpointModelVertices selector r :=
  ⟨boundaryOuterEndpoint s.graph T α, s.centralEndpointPatch_subset_model selector r
    ⟨_, ⟨α, rfl⟩, by simp⟩⟩

def endpointRootVertex (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (v : s.endpointModelRoots selector) : s.endpointModelVertices selector r :=
  ⟨v.val, ⟨v.val, v.property, by simp⟩⟩

omit [Fintype ι] in
theorem endpointBoundaryRoot_mem_central (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (α : BoundaryOrientedEdge s.graph T) :
    (s.endpointBoundaryRoot selector r α).val ∈ s.centralEndpointPatch r := by
  refine ⟨_, ⟨α, rfl⟩, ?_⟩
  change (outsideGraph s.graph T).edist (boundaryOuterEndpoint s.graph T α)
    (boundaryOuterEndpoint s.graph T α) ≤ (r : ℕ∞)
  simp

def endpointRootLabel (s : LabelledResamplingState V T ι) (selector : ℕ) :
    BoundaryOrientedEdge s.graph T ⊕ (s.AdmissibleSampleIndex selector × Fin 2) → s.endpointModelRoots selector :=
  Sum.elim (fun α => ⟨boundaryOuterEndpoint s.graph T α, Or.inl ⟨α, rfl⟩⟩)
    (fun p => Fin.cases
      ⟨s.admissibleSampleVertex selector p.1, Or.inr (Set.mem_iUnion.mpr ⟨p.1, Or.inl rfl⟩)⟩
      (fun _ => ⟨s.admissibleSecondVertex selector p.1, Or.inr (Set.mem_iUnion.mpr ⟨p.1, Or.inr rfl⟩)⟩) p.2)

omit [Fintype ι] in
theorem endpointRootLabel_surjective (s : LabelledResamplingState V T ι) (selector : ℕ) :
    Function.Surjective (s.endpointRootLabel selector) := by
  intro v
  rcases v.property with ⟨α, hα⟩ | hv
  · exact ⟨Sum.inl α, Subtype.ext hα⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
    rcases hi with h | h
    · exact ⟨Sum.inr (i, 0), Subtype.ext h.symm⟩
    · exact ⟨Sum.inr (i, 1), Subtype.ext h.symm⟩

theorem endpointRootVertex_label (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector)
    (p : BoundaryOrientedEdge s.graph T ⊕ (s.AdmissibleSampleIndex selector × Fin 2)) :
    s.endpointRootVertex selector r (s.endpointRootLabel selector p) =
      (s.endpointBranchAttachmentData selector r hsep).fullEndpoint (s.endpointBoundaryRoot selector r) p := by
  rcases p with α | ⟨i, t⟩
  · rfl
  · fin_cases t <;> rfl

def endpointCentralIso (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) :
    ((s.endpointOldGraph selector r).induce ((s.endpointBranchAttachmentData selector r hsep).core)) ≃g
      centralBoundaryGraph s.graph T r :=
  inducePreimageIso (outsideGraph s.graph T) (s.endpointModelVertices selector r)
    (s.centralEndpointPatch r) (s.centralEndpointPatch_subset_model selector r)

theorem endpoint_core_root_count [Fintype V] (s : LabelledResamplingState V T ι)
    (o : V) (ell selector r R ω : ℕ) (hT : T = graphBallVertices s.graph o ell)
    (hsep : 2 * r + 2 ≤ selector) (hmargin : ell + r + 1 ≤ R)
    (hbudget : graphBallExcess s.graph o R ≤ ω)
    (c : ((s.endpointOldGraph selector r).induce ((s.endpointBranchAttachmentData selector r hsep).core)).ConnectedComponent) :
    Nat.card {α : BoundaryOrientedEdge s.graph T //
      (s.endpointBranchAttachmentData selector r hsep).rootLabel (s.endpointBoundaryRoot selector r)
        (s.endpointBoundaryRoot_mem_central selector r) α = c} ≤ ω + 1 := by
  let D := s.endpointBranchAttachmentData selector r hsep
  let e := s.endpointCentralIso selector r hsep
  let c' := e.connectedComponentEquiv c
  let f : {α : BoundaryOrientedEdge s.graph T //
      D.rootLabel (s.endpointBoundaryRoot selector r) (s.endpointBoundaryRoot_mem_central selector r) α = c} →
      CentralBoundaryFiber s.graph T r c' := fun α =>
    ⟨α.val, congrArg e.connectedComponentEquiv α.property⟩
  have hf : Function.Injective f := fun _ _ h => Subtype.ext
    (congrArg (fun α : CentralBoundaryFiber s.graph T r c' => α.val) h)
  have hle := Nat.card_le_card_of_injective f hf
  have hbound : Nat.card (CentralBoundaryFiber s.graph T r c') ≤ ω + 1 :=
    central_boundary_fiber_card_bound_of_set_eq s.graph T o ell r R ω hT hmargin hbudget c'
  exact hle.trans hbound

theorem endpoint_post_label_count [Fintype V] (s : LabelledResamplingState V T ι)
    (o : V) (ell selector r R ω : ℕ) (hT : T = graphBallVertices s.graph o ell)
    (hsep : 2 * r + 2 ≤ selector) (hmargin : ell + r + 1 ≤ R)
    (hbudget : graphBallExcess s.graph o R ≤ ω)
    (c : (s.endpointPostGraph selector r).ConnectedComponent) :
    Nat.card {p : BoundaryOrientedEdge s.graph T ⊕ (s.AdmissibleSampleIndex selector × Fin 2) //
      (s.endpointBranchAttachmentData selector r hsep).fullEndpoint (s.endpointBoundaryRoot selector r) p ∈ c.supp} ≤
      2 * (ω + 1) := by
  let D := s.endpointBranchAttachmentData selector r hsep
  have hroot : ∀ α, s.endpointBoundaryRoot selector r α ∈ D.core :=
    s.endpointBoundaryRoot_mem_central selector r
  have hr : ∀ cc, Nat.card {α : BoundaryOrientedEdge s.graph T //
      D.rootLabel (s.endpointBoundaryRoot selector r) hroot α = cc} ≤ ω + 1 :=
    s.endpoint_core_root_count o ell selector r R ω hT hsep hmargin hbudget
  have ha : ∀ cc, Nat.card {i : s.AdmissibleSampleIndex selector // D.centralLabel i = cc} ≤ ω + 1 := by
    intro cc
    exact (D.attachFiber_card_le_rootFiber (s.endpointBoundaryRoot selector r) hroot
      (fun i => s.boundary i.val) (fun _ _ h => Subtype.ext (s.boundary.injective h)) (fun _ => rfl) cc).trans (hr cc)
  exact D.fullEndpoint_component_card_bound (s.endpointBoundaryRoot selector r) hroot (ω + 1)
    (by omega) hr ha c

theorem endpoint_post_root_count [Fintype V] (s : LabelledResamplingState V T ι)
    (o : V) (ell selector r R ω : ℕ) (hT : T = graphBallVertices s.graph o ell)
    (hsep : 2 * r + 2 ≤ selector) (hmargin : ell + r + 1 ≤ R)
    (hbudget : graphBallExcess s.graph o R ≤ ω)
    (c : (s.endpointPostGraph selector r).ConnectedComponent) :
    Nat.card {v : s.endpointModelRoots selector // s.endpointRootVertex selector r v ∈ c.supp} ≤ 2 * (ω + 1) := by
  let D := s.endpointBranchAttachmentData selector r hsep
  let F := {p : BoundaryOrientedEdge s.graph T ⊕ (s.AdmissibleSampleIndex selector × Fin 2) //
    D.fullEndpoint (s.endpointBoundaryRoot selector r) p ∈ c.supp}
  let f : F → {v : s.endpointModelRoots selector // s.endpointRootVertex selector r v ∈ c.supp} :=
    fun p => ⟨s.endpointRootLabel selector p.val, by
      rw [s.endpointRootVertex_label selector r hsep]
      exact p.property⟩
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨p, hp⟩ := s.endpointRootLabel_surjective selector v.val
    have hmem : D.fullEndpoint (s.endpointBoundaryRoot selector r) p ∈ c.supp := by
      rw [← s.endpointRootVertex_label selector r hsep, hp]
      exact v.property
    exact ⟨⟨p, hmem⟩, Subtype.ext hp⟩
  exact (Nat.card_le_card_of_surjective f hf).trans
    (s.endpoint_post_label_count o ell selector r R ω hT hsep hmargin hbudget c)

end LabelledResamplingState
end LocalLaw
