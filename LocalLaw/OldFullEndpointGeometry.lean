import LocalLaw.FullEndpointAmbientDiameter
import LocalLaw.SourceFilledEndpointBudget
import LocalLaw.FullEndpointPerturbation
import LocalLaw.OldEndpointComponentCounts
import LocalLaw.FilledEndpointLocality

/-! # The old full benchmark inherits its class from one actual root ball

Its central component is the expanded retained ball. Every other component
is contained in one of the genuine isolated sampled tree patches.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance oldFullEndpointGeometryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) oldFullEndpointComponentDecidable {A : Type*}
    (G : SimpleGraph A) (C : G.ConnectedComponent) : DecidablePred (fun x => x ∈ C.supp) :=
  fun _ => Classical.propDecidable _

theorem filled_captures_outside_ball {V : Type} (G : SimpleGraph V) (T : Set V)
    (K : Set (Tᶜ : Set V)) (r : ℕ)
    (hboundary : ∀ a : BoundaryOrientedEdge G T,
      graphBallVertices (outsideGraph G T) (boundaryOutsideVertex G T a) r ⊆ K)
    (x : (Tᶜ : Set V)) (hx : graphBallVertices (outsideGraph G T) x r ⊆ K) :
    graphBallVertices G x.val r ⊆ filledExteriorVertices T K := by
  intro y hy
  by_cases hyt : y ∈ T
  · exact Or.inl hyt
  · obtain ⟨p, hp⟩ := graphBall_exists_walk_length_le G x.val y r hy
    rcases walk_outside_or_last_exit G T p hyt with ⟨_, q, hlen⟩ | ⟨a, pref, q, hlen⟩
    · exact Or.inr ⟨⟨y, hyt⟩, hx ((SimpleGraph.edist_le q).trans
        (ENat.coe_le_coe.mpr (by omega))), rfl⟩
    · exact Or.inr ⟨⟨y, hyt⟩, hboundary a ((SimpleGraph.edist_le q).trans
        (ENat.coe_le_coe.mpr (by omega))), rfl⟩

namespace LabelledResamplingState
variable {V : Type} [Fintype V] {T : Set V} {ι : Type} [Fintype ι]

omit [Fintype V] [Fintype ι] in
theorem fullEndpoint_old_root_ball_capture (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (x : s.fullEndpointRoots selector) :
    graphBallVertices s.graph x.val r ⊆ filledExteriorVertices T (s.endpointModelVertices selector r) := by
  have hboundary (a : BoundaryOrientedEdge s.graph T) :
      graphBallVertices (outsideGraph s.graph T) (boundaryOutsideVertex s.graph T a) r ⊆
        s.endpointModelVertices selector r := fun y hy => ⟨_, Or.inl ⟨a, rfl⟩, hy⟩
  rcases x.property with hx | ⟨y, hy, heq⟩
  · exact (graphBallVertices_mono s.graph x.val (Nat.le_succ r)).trans
      (filled_captures_inner_ball s.graph T _ r hboundary ⟨x.val, hx⟩)
  · have hx : graphBallVertices (outsideGraph s.graph T) y r ⊆ s.endpointModelVertices selector r :=
      fun v hv => ⟨y, hy, hv⟩
    have hh := filled_captures_outside_ball s.graph T _ r hboundary y hx
    rwa [heq] at hh

end LabelledResamplingState

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem old_filledEndpoint_component_budget (g : RegularGraph N d) (o : Fin N)
    (ell selector r R : ℕ) (hsep : 2 * r + 2 ≤ selector) (hmargin : ell + r + 1 ≤ R)
    (hbudget : graphBallExcess g.graph o R ≤ finiteOmega d)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) :
    let T := graphBallVertices g.graph o ell
    let s := g.admissibleState T boundary samples
    (g.filledExteriorModel T (s.endpointModelVertices selector r)).ComponentReferenceBudget := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  let K := filledExteriorVertices T (s.endpointModelVertices selector r)
  let L := filledExteriorVertices T (s.centralEndpointPatch r)
  let M := g.filledExteriorModel T (s.endpointModelVertices selector r)
  have hL : L = graphBallVertices g.graph o (ell + r + 1) := filled_centralBoundary_eq_ball g.graph o ell r
  intro c
  change (∑ v, (M.restrict c.supp).deficit v) + graphExcess (M.restrict c.supp).graph ≤ finiteOmega d
  have hzero : ∀ v, (M.restrict c.supp).deficit v = 0 := fun _ => rfl
  simp only [hzero, Finset.sum_const_zero, zero_add]
  obtain ⟨a, ha⟩ := c.nonempty_supp
  let root : c.supp := ⟨a, ha⟩
  by_cases hc : a.val ∈ L
  · have hsub := induced_component_subset_of_closed s.graph K L
      (s.fullEndpoint_old_core_closed selector r hsep) c root hc
    let f : (M.graph.induce c.supp) →g graphBall g.graph o (ell + r + 1) :=
      { toFun := fun x => ⟨x.val.val, hL ▸ hsub x⟩
        map_rel' := fun h => h }
    have hf : Function.Injective f := fun _ _ h =>
      Subtype.ext (Subtype.ext (congrArg (fun v : graphBallVertices g.graph o (ell + r + 1) => v.val) h))
    exact (connected_embedding_graphExcess_le _ _ c.connected_induce_supp
      (graphBall_connected g.graph o (ell + r + 1)) f hf).trans
        ((graphBallExcess_mono_radius g.graph o hmargin).trans hbudget)
  · have hout : a.val ∉ T := fun h => hc (Or.inl h)
    let aa : (Tᶜ : Set (Fin N)) := ⟨a.val, hout⟩
    have haK := (filledExterior_outside_mem T (s.endpointModelVertices selector r) aa).mp a.property
    rcases s.endpointModelVertices_cell_cover selector r aa haK with hcentral | ⟨i, hi⟩
    · exact False.elim (hc (Or.inr ⟨aa, hcentral, rfl⟩))
    · have hsub := induced_component_subset_of_closed s.graph K (s.fullSampledPatch selector r i)
        (s.fullEndpoint_old_sampled_closed selector r hsep i) c root ⟨aa, hi, rfl⟩
      have houtside (x : c.supp) : x.val.val ∉ T := by
        obtain ⟨v, _, hv⟩ := hsub x
        exact hv ▸ v.property
      have hmem (x : c.supp) : (⟨x.val.val, houtside x⟩ : (Tᶜ : Set (Fin N))) ∈ s.sampledEndpointPatch selector r i := by
        obtain ⟨v, hv, heq⟩ := hsub x
        exact (Subtype.ext heq : v = ⟨x.val.val, houtside x⟩) ▸ hv
      let f : (M.graph.induce c.supp) →g
          (outsideGraph g.graph T).induce (s.sampledEndpointPatch selector r i) :=
        { toFun := fun x => ⟨⟨x.val.val, houtside x⟩, hmem x⟩
          map_rel' := fun h => h }
      have hf : Function.Injective f := fun _ _ h =>
        Subtype.ext (Subtype.ext (congrArg (fun v : s.sampledEndpointPatch selector r i => v.val.val) h))
      have ht := s.sampledEndpointPatch_isTree selector r (by omega) i
      have ht' : ((outsideGraph g.graph T).induce (s.sampledEndpointPatch selector r i)).IsTree := ht
      have hh := connected_embedding_graphExcess_le _ _ c.connected_induce_supp ht'.isConnected f hf
      rw [tree_graphExcess_zero _ ht'] at hh
      exact hh.trans (Nat.zero_le _)

omit [Fintype ι] in
theorem old_filledEndpoint_distance_bound (g : RegularGraph N d) (o : Fin N)
    (ell selector r R : ℕ) (hsep : 2 * r + 2 ≤ selector) (hmargin : ell + r + 1 ≤ R)
    (hbudget : graphBallExcess g.graph o R ≤ finiteOmega d)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) :
    let T := graphBallVertices g.graph o ell
    let s := g.admissibleState T boundary samples
    ∀ x y, (g.filledExteriorModel T (s.endpointModelVertices selector r)).graph.dist x y ≤
      filledEndpointDiameter d ell r := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  let K := s.endpointModelVertices selector r
  let G := g.graph.induce (filledExteriorVertices T K)
  let S := filledExteriorInner T K
  let e := filledInnerGraphIso g.graph T K
  have hS : (G.induce S).Connected := e.connected_iff.mpr (graphBall_connected g.graph o ell)
  have hinner : ∀ x y : S, (G.induce S).dist x y ≤ 2 * ell := by
    intro x y
    rw [← graphIso_dist e x y]
    exact graphBall_distance_le_twice_radius g.graph o ell (e x) (e y)
  have hcount := g.endpointModel_old_component_root_count o ell selector r R (finiteOmega d)
    hmargin hsep hbudget boundary samples
  have houter : ∀ x y : (Sᶜ : Set (filledExteriorVertices T K)),
      (outsideGraph G S).dist x y ≤ (2 * (finiteOmega d + 1)) * (2 * r + 1) := by
    intro x y
    let f := filledExteriorOutsideIso g.graph T K
    rw [← graphIso_dist f x y]
    exact s.endpointModel_old_distance_bound selector r (2 * (finiteOmega d + 1)) (by omega) hcount (f x) (f y)
  exact graph_distance_from_inner_outside G S hS (2 * ell) _ hinner houter

end RegularGraph
end LocalLaw
