import LocalLaw.CentralEndpointCharges
import LocalLaw.EndpointModelDiameter
import LocalLaw.IsolatedCellRoots

/-!
# Actual root counts in old endpoint-model components

The original central patch contains only old boundary roots, counted by the
cutset charge. An isolated sampled patch contains only its own two roots.
Actual old no-cross-edge geometry prevents a component from mixing cells.
-/

noncomputable section
namespace LocalLaw
local instance oldEndpointCountsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} [Fintype V] {T : Set V} {ι : Type*}

omit [Fintype V] in
theorem endpointModelVertices_cell_cover (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (v : (Tᶜ : Set V)) (hv : v ∈ s.endpointModelVertices selector r) :
    v ∈ s.centralEndpointPatch r ∨ ∃ i, v ∈ s.sampledEndpointPatch selector r i := by
  obtain ⟨a, ha, hd⟩ := hv
  rcases ha with ha | ha
  · exact Or.inl ⟨a, ha, hd⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
    exact Or.inr ⟨i, a, hi, hd⟩

omit [Fintype V] in
theorem endpointModel_central_closed (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) :
    ∀ u ∈ s.endpointModelVertices selector r, u ∈ s.centralEndpointPatch r →
      ∀ v ∈ s.endpointModelVertices selector r, v ∉ s.centralEndpointPatch r →
        ¬(outsideGraph s.graph T).Adj u v := by
  intro u _ hu v hv hn huv
  rcases s.endpointModelVertices_cell_cover selector r v hv with hv | ⟨i, hi⟩
  · exact hn hv
  · exact (s.central_sampledEndpointPatch_disjoint_no_edge selector r hsep i).2 u hu v hi huv

omit [Fintype V] in
theorem endpointModel_sampled_closed (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    ∀ u ∈ s.endpointModelVertices selector r, u ∈ s.sampledEndpointPatch selector r i →
      ∀ v ∈ s.endpointModelVertices selector r, v ∉ s.sampledEndpointPatch selector r i →
        ¬(outsideGraph s.graph T).Adj u v := by
  intro u _ hu v hv hn huv
  rcases s.endpointModelVertices_cell_cover selector r v hv with hv | ⟨j, hj⟩
  · exact (s.central_sampledEndpointPatch_disjoint_no_edge selector r hsep i).2 v hv u hu huv.symm
  · by_cases hji : j = i
    · subst j; exact hn hj
    · exact (s.sampledEndpointPatches_disjoint_no_edge selector r (by omega) i j
        (Ne.symm hji)).2 u hu v hj huv

omit [Fintype V] in
theorem endpointRoot_in_central_is_boundary (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector) (v : s.endpointModelRoots selector)
    (hv : v.val ∈ s.centralEndpointPatch r) :
    ∃ α : BoundaryOrientedEdge s.graph T, boundaryOuterEndpoint s.graph T α = v.val := by
  rcases v.property with hv0 | hv0
  · exact hv0
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv0
    have hp : v.val ∈ s.sampledEndpointPatch selector r i := ⟨v.val, hi, by simp⟩
    exact False.elim (Set.disjoint_left.mp
      (s.central_sampledEndpointPatch_disjoint_no_edge selector r hsep i).1 hv hp)

omit [Fintype V] in
theorem endpointRoot_in_sampled_is_pair (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector) (i : s.AdmissibleSampleIndex selector)
    (v : s.endpointModelRoots selector) (hv : v.val ∈ s.sampledEndpointPatch selector r i) :
    v.val ∈ s.admissiblePairRoots selector i := by
  rcases v.property with hv0 | hv0
  · have hc : v.val ∈ s.centralEndpointPatch r := ⟨v.val, hv0, by simp⟩
    exact False.elim (Set.disjoint_left.mp
      (s.central_sampledEndpointPatch_disjoint_no_edge selector r hsep i).1 hc hv)
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hv0
    by_cases hji : j = i
    · exact hji ▸ hj
    · have hp : v.val ∈ s.sampledEndpointPatch selector r j := ⟨v.val, hj, by simp⟩
      exact False.elim (Set.disjoint_left.mp
        (s.sampledEndpointPatches_disjoint_no_edge selector r (by omega) i j (Ne.symm hji)).1 hv hp)

end LabelledResamplingState

namespace RegularGraph
variable {N d : ℕ} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem endpointModel_old_component_root_count (g : RegularGraph N d) (o : Fin N)
    (ell selector r R ω : ℕ) (hmargin : ell + r + 1 ≤ R) (hsep : 2 * r + 2 ≤ selector)
    (hbudget : graphBallExcess g.graph o R ≤ ω)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) :
    let T := graphBallVertices g.graph o ell
    let s := g.admissibleState T boundary samples
    ∀ c : ((outsideGraph s.graph T).induce (s.endpointModelVertices selector r)).ConnectedComponent,
      Nat.card {a : s.endpointModelRoots selector // s.endpointModelKernelEmbedding selector r a ∈ c.supp} ≤
        2 * (ω + 1) := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  let H := outsideGraph s.graph T
  let K := s.endpointModelVertices selector r
  let center := s.endpointModelKernelEmbedding selector r
  intro c
  let x : c.supp := Classical.choice c.connected_induce_supp.nonempty
  rcases s.endpointModelVertices_cell_cover selector r x.val.val x.val.property with hc | ⟨i, hi⟩
  · have hsub := induced_component_subset_of_closed H K (s.centralEndpointPatch r)
      (s.endpointModel_central_closed selector r hsep) c x hc
    apply induced_component_root_card_le_isolated_cell H K (s.centralEndpointPatch r) center c hsub
      (2 * (ω + 1))
    intro C
    let F := {a : s.endpointModelRoots selector //
      ∃ ha : (center a).val ∈ s.centralEndpointPatch r,
        (⟨(center a).val, ha⟩ : s.centralEndpointPatch r) ∈ C.supp}
    have houter (a : F) : ∃ α : BoundaryOrientedEdge g.graph T,
        boundaryOuterEndpoint g.graph T α = a.val.val :=
      s.endpointRoot_in_central_is_boundary selector r hsep a.val (Classical.choose a.property)
    let f : F → CentralBoundaryFiber g.graph T r C := fun a =>
      ⟨Classical.choose (houter a), by
        obtain ⟨ha, hmem⟩ := a.property
        have heq : centralBoundaryCenter g.graph T r (Classical.choose (houter a)) =
            (⟨a.val.val, ha⟩ : centralBoundaryVertices g.graph T r) :=
          Subtype.ext (Classical.choose_spec (houter a))
        rw [heq]
        exact hmem⟩
    have hf : Function.Injective f := by
      intro a b hab
      have hlabel : (f a).val = (f b).val := congrArg
        (fun z : CentralBoundaryFiber g.graph T r C => z.val) hab
      have hval : a.val.val = b.val.val := (Classical.choose_spec (houter a)).symm.trans
        ((congrArg (boundaryOuterEndpoint g.graph T) hlabel).trans (Classical.choose_spec (houter b)))
      exact Subtype.ext (Subtype.ext hval)
    letI : Fintype (CentralBoundaryFiber g.graph T r C) := by
      unfold CentralBoundaryFiber
      infer_instance
    have hh := (Nat.card_le_card_of_injective f hf).trans
      (central_boundary_fiber_card_bound g.graph o ell r R ω hmargin hbudget C)
    exact hh.trans (by omega)
  · have hsub := induced_component_subset_of_closed H K (s.sampledEndpointPatch selector r i)
      (s.endpointModel_sampled_closed selector r hsep i) c x hi
    apply induced_component_root_card_le_isolated_cell H K (s.sampledEndpointPatch selector r i) center c hsub
      (2 * (ω + 1))
    intro C
    let F := {a : s.endpointModelRoots selector //
      ∃ ha : (center a).val ∈ s.sampledEndpointPatch selector r i,
        (⟨(center a).val, ha⟩ : s.sampledEndpointPatch selector r i) ∈ C.supp}
    let f : F → s.admissiblePairRoots selector i := fun a =>
      ⟨a.val.val, s.endpointRoot_in_sampled_is_pair selector r hsep i a.val (Classical.choose a.property)⟩
    have hf : Function.Injective f := by
      intro a b hab
      have hval : a.val.val = b.val.val := congrArg
        (fun z : s.admissiblePairRoots selector i => z.val) hab
      exact Subtype.ext (Subtype.ext hval)
    have hpair : Nat.card (s.admissiblePairRoots selector i) ≤ 2 := by
      change ({s.admissibleSampleVertex selector i, s.admissibleSecondVertex selector i} : Set (Tᶜ : Set (Fin N))).ncard ≤ 2
      exact (Set.ncard_insert_le _ _).trans (by simp only [Set.ncard_singleton]; omega)
    exact ((Nat.card_le_card_of_injective f hf).trans hpair).trans (by omega)

end RegularGraph
end LocalLaw
