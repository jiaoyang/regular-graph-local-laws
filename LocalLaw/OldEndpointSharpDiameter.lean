import LocalLaw.OldEndpointComponentCounts

/-!
# Actual root counts in old endpoint-model components

The original central patch contains only old boundary roots, counted by the
cutset charge. An isolated sampled patch contains only its own two roots.
Actual old no-cross-edge geometry prevents a component from mixing cells.
-/

noncomputable section
namespace LocalLaw
local instance oldEndpointSharpDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem endpointModel_old_component_root_count_sharp (g : RegularGraph N d) (o : Fin N)
    (ell selector r R ω : ℕ) (hω : 1 ≤ ω) (hmargin : ell + r + 1 ≤ R) (hsep : 2 * r + 2 ≤ selector)
    (hbudget : graphBallExcess g.graph o R ≤ ω)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) :
    let T := graphBallVertices g.graph o ell
    let s := g.admissibleState T boundary samples
    ∀ c : ((outsideGraph s.graph T).induce (s.endpointModelVertices selector r)).ConnectedComponent,
      Nat.card {a : s.endpointModelRoots selector // s.endpointModelKernelEmbedding selector r a ∈ c.supp} ≤
        ω + 1 := by
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
      (ω + 1)
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
      (ω + 1)
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

omit [Fintype ι] in
/-- The sharp old root count gives a diameter independent of the total
number of sampled patches. -/
theorem endpointModel_old_distance_bound_sharp (g : RegularGraph N d) (o : Fin N)
    (ell selector r R ω : ℕ) (hω : 1 ≤ ω) (hmargin : ell + r + 1 ≤ R)
    (hsep : 2*r+2 ≤ selector) (hbudget : graphBallExcess g.graph o R ≤ ω)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) :
    let T := graphBallVertices g.graph o ell
    let s := g.admissibleState T boundary samples
    ∀ x y : s.endpointModelVertices selector r,
      ((outsideGraph s.graph T).induce (s.endpointModelVertices selector r)).dist x y ≤
        (ω+1)*(2*r+1) := by
  dsimp only
  let s := g.admissibleState (graphBallVertices g.graph o ell) boundary samples
  exact s.endpointModel_old_distance_bound selector r (ω+1) (by omega)
    (g.endpointModel_old_component_root_count_sharp o ell selector r R ω hω hmargin hsep hbudget boundary samples)

end RegularGraph
end LocalLaw
