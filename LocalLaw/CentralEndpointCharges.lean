import LocalLaw.AdmissibleEndpointModel
import LocalLaw.DeletedNeighborhoodDiameter

/-! # Actual boundary-label and deficit charges in a central endpoint cell

Every central component embeds in one original annulus component. Its
boundary labels therefore have the actual cutset count bound. For a regular
graph the inherited deleted deficit sum is exactly the number of these
labels, including repeated outside endpoints.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
namespace LocalLaw

local instance centralEndpointChargesDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) canonicalCentralEndpointChargesMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

variable {V : Type*}

def centralBoundaryVertices (G : SimpleGraph V) (T : Set V) (r : ℕ) : Set (Tᶜ : Set V) :=
  graphSetBall (outsideGraph G T) (outerBoundaryRoots G T) r

def centralBoundaryGraph (G : SimpleGraph V) (T : Set V) (r : ℕ) :=
  (outsideGraph G T).induce (centralBoundaryVertices G T r)

def centralBoundaryCenter (G : SimpleGraph V) (T : Set V) (r : ℕ)
    (α : BoundaryOrientedEdge G T) : centralBoundaryVertices G T r :=
  ⟨boundaryOuterEndpoint G T α, boundaryOuterEndpoint G T α, ⟨α, rfl⟩, by simp⟩

def CentralBoundaryFiber (G : SimpleGraph V) (T : Set V) (r : ℕ)
    (c : (centralBoundaryGraph G T r).ConnectedComponent) :=
  {α : BoundaryOrientedEdge G T // centralBoundaryCenter G T r α ∈ c.supp}

theorem centralBoundaryVertices_subset_original_ball (G : SimpleGraph V) (o : V)
    (ell r R : ℕ) (hmargin : ell + r + 1 ≤ R) :
    ∀ v ∈ centralBoundaryVertices G (graphBallVertices G o ell) r,
      v.val ∈ graphBallVertices G o R := by
  rintro v ⟨a, ⟨α, rfl⟩, hd⟩
  let T := graphBallVertices G o ell
  have hhead : α.val.2 ∈ graphBallVertices G o (ell + 1) :=
    adjacent_inner_mem_outer_ball G o le_rfl α.property.2.1 α.property.1
  have htail := (graphHom_edist_le (SimpleGraph.Embedding.induce (G := G) Tᶜ).toHom
    (boundaryOuterEndpoint G T α) v).trans hd
  apply ((SimpleGraph.edist_triangle (G := G) (u := o) (v := α.val.2)).trans
    (add_le_add hhead htail)).trans
  exact_mod_cast (show ell + 1 + r ≤ R by omega)

variable [Fintype V]

theorem central_boundary_fiber_card_le_ambient (G : SimpleGraph V) (o : V)
    (ell r R : ℕ) (hmargin : ell + r + 1 ≤ R)
    (c : (centralBoundaryGraph G (graphBallVertices G o ell) r).ConnectedComponent)
    (α : BoundaryOrientedEdge G (graphBallVertices G o ell))
    (hα : centralBoundaryCenter G (graphBallVertices G o ell) r α ∈ c.supp) :
    Nat.card (CentralBoundaryFiber G (graphBallVertices G o ell) r c) ≤
      Nat.card (AmbientBallBoundaryFiber G o (by omega : ell + 1 ≤ R)
        (ambientBoundaryComponent G o (by omega : ell + 1 ≤ R) α)) := by
  let T := graphBallVertices G o ell
  let hR : ell + 1 ≤ R := by omega
  let C := ambientBoundaryComponent G o hR α
  let H := centralBoundaryGraph G T r
  let f : H.induce c.supp →g outsideGraph (graphBall G o R) (ballCutInner G o ell R) :=
    { toFun := fun x => ⟨⟨x.val.val.val,
        centralBoundaryVertices_subset_original_ball G o ell r R hmargin x.val.val x.val.property⟩,
        x.val.val.property⟩
      map_rel' := fun h => h }
  have hsame : ∀ e : CentralBoundaryFiber G T r c, ambientBoundaryComponent G o hR e.val = C := by
    intro e
    let a : c.supp := ⟨centralBoundaryCenter G T r α, hα⟩
    let b : c.supp := ⟨centralBoundaryCenter G T r e.val, e.property⟩
    obtain ⟨p⟩ := c.connected_induce_supp.preconnected a b
    exact (SimpleGraph.ConnectedComponent.sound (p.map f).reachable).symm
  let enc : CentralBoundaryFiber G T r c → AmbientBallBoundaryFiber G o hR C :=
    fun e => ⟨e.val, hsame e⟩
  have hinj : Function.Injective enc := by
    intro e f he
    exact Subtype.ext (congrArg (fun v : AmbientBallBoundaryFiber G o hR C => v.val) he)
  exact Nat.card_le_card_of_injective enc hinj

theorem central_boundary_fiber_card_bound (G : SimpleGraph V) (o : V)
    (ell r R ω : ℕ) (hmargin : ell + r + 1 ≤ R) (hbudget : graphBallExcess G o R ≤ ω)
    (c : (centralBoundaryGraph G (graphBallVertices G o ell) r).ConnectedComponent) :
    Nat.card (CentralBoundaryFiber G (graphBallVertices G o ell) r c) ≤ ω + 1 := by
  by_cases hnon : Nonempty (CentralBoundaryFiber G (graphBallVertices G o ell) r c)
  · let e := Classical.choice hnon
    exact (central_boundary_fiber_card_le_ambient G o ell r R hmargin c e.val e.property).trans
      (ambient_boundary_component_count_bound G o (by omega : ell + 1 ≤ R) hbudget _)
  · letI : IsEmpty (CentralBoundaryFiber G (graphBallVertices G o ell) r c) := ⟨fun e => hnon ⟨e⟩⟩
    simp only [Nat.card_of_isEmpty]
    exact Nat.zero_le _

def centralBoundaryNeighborEquiv (G : SimpleGraph V) (T : Set V) (r : ℕ)
    (c : (centralBoundaryGraph G T r).ConnectedComponent) :
    (Σ v : c.supp, {t : T // G.Adj t.val v.val.val.val}) ≃ CentralBoundaryFiber G T r c where
  toFun w :=
    let α : BoundaryOrientedEdge G T :=
      ⟨(w.2.val.val, w.1.val.val.val), w.2.property, w.2.val.property, w.1.val.val.property⟩
    ⟨α, by
      have heq : centralBoundaryCenter G T r α = w.1.val := Subtype.ext (Subtype.ext rfl)
      rw [heq]
      exact w.1.property⟩
  invFun e := ⟨⟨centralBoundaryCenter G T r e.val, e.property⟩,
    ⟨⟨e.val.val.1, e.val.property.2.1⟩, e.val.property.1⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace RegularGraph
variable {N d : ℕ}

theorem central_component_deficit_sum_eq_labels (g : RegularGraph N d) (T : Set (Fin N)) (r : ℕ)
    (c : (centralBoundaryGraph g.graph T r).ConnectedComponent) :
    (∑ v : c.supp, (((g.deficient.delete T).restrict (centralBoundaryVertices g.graph T r)).restrict c.supp).deficit v) =
      Nat.card (CentralBoundaryFiber g.graph T r c) := by
  have hh := Nat.card_congr (centralBoundaryNeighborEquiv g.graph T r c)
  rw [Nat.card_sigma] at hh
  have hdef : ∀ v : c.supp,
      (((g.deficient.delete T).restrict (centralBoundaryVertices g.graph T r)).restrict c.supp).deficit v =
        Nat.card {t : T // g.graph.Adj t.val v.val.val.val} := by
    intro v
    change (g.deficient.delete T).deficit v.val.val = _
    rw [g.deficient.delete_deficit_eq_removed_neighbors]
    change 0 + Nat.card {t : T // g.graph.Adj t.val v.val.val.val} = _
    exact Nat.zero_add _
  exact (Finset.sum_congr rfl (fun v _ => hdef v)).trans hh

end RegularGraph
end LocalLaw
