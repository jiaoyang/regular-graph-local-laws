import LocalLaw.CutComponentDiameter
import LocalLaw.EndpointModelDiameter
import LocalLaw.FilledExteriorModel
import LocalLaw.EndpointComponentCounts
import LocalLaw.SwitchedRetainedReference
import LocalLaw.TreeRadiusStability

/-! # Rejoining a connected retained set gives a uniform diameter

Only the actual intrinsic diameter of the retained graph and of its deleted
complement are used. The full graph may be disconnected.
-/

noncomputable section
namespace LocalLaw
local instance filledModelDiameterDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

theorem reachable_outside_of_no_inner (G : SimpleGraph V) (S : Set V)
    {x y : V} (p : G.Walk x y) (hx : x∉S) (hy : y∉S)
    (hno : ∀ t∈S, ¬G.Reachable x t) : (outsideGraph G S).Reachable ⟨x,hx⟩ ⟨y,hy⟩ := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x u y hxu p ih =>
    have hu : u∉S := fun h => hno u h hxu.reachable
    have hnou : ∀ t∈S, ¬G.Reachable u t := fun t ht h => hno t ht (hxu.reachable.trans h)
    exact (show (outsideGraph G S).Adj ⟨x,hx⟩ ⟨u,hu⟩ from hxu).reachable.trans (ih hu hy hnou)

theorem short_walk_to_inner (G : SimpleGraph V) (S : Set V) (R : ℕ)
    (hR : ∀ a b : (Sᶜ : Set V), (outsideGraph G S).dist a b≤R)
    {x t : V} (hxt : G.Reachable x t) (ht : t∈S) :
    ∃ a : S, ∃ p : G.Walk x a.val, p.length≤R+1 := by
  by_cases hx : x∈S
  · exact ⟨⟨x,hx⟩,SimpleGraph.Walk.nil,Nat.zero_le _⟩
  obtain ⟨p⟩ := hxt
  obtain ⟨u,hu,v,hv,huv,q,_⟩ : ∃ (u : V) (_hu : u∉Sᶜ) (v : V) (hv : v∈Sᶜ) (_huv : G.Adj u v),
      ∃ q : (G.induce Sᶜ).Walk ⟨v,hv⟩ ⟨x,hx⟩, q.length+1≤p.reverse.length := by
    rcases walk_last_set_entry G Sᶜ p.reverse hx with ⟨ht',_,_⟩ | h
    · exact False.elim (ht' ht)
    · exact h
  have huS : u∈S := by simpa only [Set.mem_compl_iff,not_not] using hu
  obtain ⟨a,ha⟩ := q.reverse.reachable.exists_walk_length_eq_dist
  let hom : outsideGraph G S →g G := ⟨Subtype.val,fun h => h⟩
  refine ⟨⟨u,huS⟩,(a.map hom).concat huv.symm,?_⟩
  simp only [SimpleGraph.Walk.length_concat,SimpleGraph.Walk.length_map,ha]
  exact Nat.succ_le_succ (hR _ _)

theorem graph_distance_from_inner_outside (G : SimpleGraph V) (S : Set V)
    (hS : (G.induce S).Connected) (Rin Rout : ℕ)
    (hinner : ∀ a b : S, (G.induce S).dist a b≤Rin)
    (houter : ∀ a b : (Sᶜ : Set V), (outsideGraph G S).dist a b≤Rout)
    (x y : V) : G.dist x y≤Rin+2*(Rout+1) := by
  by_cases hxy : G.Reachable x y
  · by_cases hhit : ∃ t∈S,G.Reachable x t
    · obtain ⟨t,ht,hxt⟩ := hhit
      obtain ⟨a,pa,hpa⟩ := short_walk_to_inner G S Rout houter hxt ht
      obtain ⟨b,pb,hpb⟩ := short_walk_to_inner G S Rout houter (hxy.symm.trans hxt) ht
      obtain ⟨q,hq⟩ := hS.exists_walk_length_eq_dist a b
      let hom : G.induce S →g G := ⟨Subtype.val,fun h => h⟩
      have hh := G.dist_le (pa.append ((q.map hom).append pb.reverse))
      simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_map,SimpleGraph.Walk.length_reverse,hq] at hh
      have hcore := hinner a b
      omega
    · have hno : ∀ t∈S,¬G.Reachable x t := by
        intro t ht hr
        exact hhit ⟨t,ht,hr⟩
      have hx : x∉S := fun h => hno x h (SimpleGraph.Reachable.refl _)
      have hy : y∉S := fun h => hno y h hxy
      obtain ⟨p⟩ := hxy
      have hout := reachable_outside_of_no_inner G S p hx hy hno
      obtain ⟨q,hq⟩ := hout.exists_walk_length_eq_dist
      let hom : outsideGraph G S →g G := ⟨Subtype.val,fun h => h⟩
      have hh := G.dist_le (q.map hom)
      simp only [SimpleGraph.Walk.length_map,hq] at hh
      exact hh.trans ((houter _ _).trans (by omega))
  · rw [SimpleGraph.dist_eq_zero_of_not_reachable hxy]
    exact Nat.zero_le _


def filledInnerGraphIso (G : SimpleGraph V) (T : Set V) (K : Set (Tᶜ : Set V)) :
    ((G.induce (filledExteriorVertices T K)).induce (filledExteriorInner T K)) ≃g G.induce T where
  toEquiv := filledExteriorInnerEquiv T K
  map_rel_iff' := Iff.rfl

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem filledEndpoint_distance_bound (g : RegularGraph N d)
    (o : Fin N) (ell selector r R ω : ℕ)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (hsep : 2*r+2≤selector) (hmargin : ell+r+1≤R)
    (hex : graphBallExcess g.graph o R≤ω) :
    let T := graphBallVertices g.graph o ell
    let s := g.admissibleState T boundary samples
    let M := (g.labelledResampledGraph T boundary samples selector).filledExteriorModel T
      (s.endpointModelVertices selector r)
    ∀ x y, M.graph.dist x y≤2*ell+2*((2*(ω+1))*(2*r+1)+1) := by
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  let K := s.endpointModelVertices selector r
  let gnew := g.labelledResampledGraph T boundary samples selector
  let G := gnew.graph.induce (filledExteriorVertices T K)
  let S := filledExteriorInner T K
  let e := filledInnerGraphIso gnew.graph T K
  have hT : (gnew.graph.induce T).Connected := by
    rw [show gnew.graph.induce T=g.graph.induce T from s.fullResample_induce selector]
    exact graphBall_connected g.graph o ell
  have hS : (G.induce S).Connected := e.connected_iff.mpr hT
  have hinner : ∀ a b:S,(G.induce S).dist a b≤2*ell := by
    intro a b
    have hh := graphIso_dist e a b
    change (gnew.graph.induce T).dist ((filledExteriorInnerEquiv T K) a)
      ((filledExteriorInnerEquiv T K) b)=(G.induce S).dist a b at hh
    rw [show gnew.graph.induce T=g.graph.induce T from s.fullResample_induce selector] at hh
    rw [←hh]
    exact graphBall_distance_le_twice_radius g.graph o ell
      ((filledExteriorInnerEquiv T K) a) ((filledExteriorInnerEquiv T K) b)
  have hcount : ∀ C:(s.endpointPostGraph selector r).ConnectedComponent,
      Nat.card {i:s.endpointModelRoots selector // s.endpointModelKernelEmbedding selector r i∈C.supp}≤2*(ω+1) :=
    s.endpoint_post_root_count o ell selector r R ω rfl hsep hmargin hex
  have houter : ∀ a b:(Sᶜ:Set (filledExteriorVertices T K)),
      (outsideGraph G S).dist a b≤(2*(ω+1))*(2*r+1) := by
    intro a b
    let f := filledExteriorOutsideIso gnew.graph T K
    rw [←graphIso_dist f a b]
    exact s.endpointModel_new_distance_bound selector r (2*(ω+1)) (by omega) hcount (f a) (f b)
  exact graph_distance_from_inner_outside G S hS (2*ell) ((2*(ω+1))*(2*r+1)) hinner houter

end RegularGraph

end LocalLaw
