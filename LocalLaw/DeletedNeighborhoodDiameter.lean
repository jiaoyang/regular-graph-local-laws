import LocalLaw.DeletedNeighborhoodCover

/-!
# Derived intrinsic diameter after deleting the inner neighborhood

Every covering component containing a boundary center lies in the actual
outer annulus. Its boundary labels therefore inject into one actual annulus
fiber, whose size is at most omega+1. Two additional target centers give the
derived bound omega+3, independently of the total boundary size.
-/

noncomputable section
namespace LocalLaw
local instance deletedNeighborhoodDiameterDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

/-- A deleted-cover component attached to the removed ball stays in the
actual outer ball. Containment follows from the full three-ball diameter. -/
theorem deletedNeighborhoodCover_component_outer (G : SimpleGraph V) (o i j : V)
    (ell r R : ℕ) (hr : 1 ≤ r)
    (hi : i ∉ graphBallVertices G o ell) (hj : j ∉ graphBallVertices G o ell)
    (hmargin : 6 * (ell + r) + 2 ≤ R)
    (c : (deletedNeighborhoodCoverGraph G o i j ell r hi hj).ConnectedComponent)
    (e : BoundaryOrientedEdge G (graphBallVertices G o ell))
    (he : deletedNeighborhoodCenterVertex G o i j ell r hi hj (Sum.inl e) ∈ c.supp)
    (x : ballCoverVertices (outsideGraph G (graphBallVertices G o ell))
      (deletedNeighborhoodCoverCenter G o i j ell hi hj) (deletedNeighborhoodCoverRadius G o ell r))
    (hx : x ∈ c.supp) : x.val.val ∈ graphBallVertices G o R := by
  let Go := deletionNeighborhoodGraph G o i j ell r
  let root := deletionNeighborhoodRoot G o i j ell r
  let φ := deletedNeighborhoodCoverIso G o i j ell r hr hi hj
  let ce := deletedNeighborhoodCenterVertex G o i j ell r hi hj (Sum.inl e)
  let l : deletionNeighborhoodVertices G o i j ell r :=
    ⟨e.val.1, deletionNeighborhood_contains_root_ball G o i j ell r e.property.2.1⟩
  have hl : l ∈ graphBallVertices Go root ell :=
    (deletionNeighborhood_inner_mem G o i j ell r l).mpr e.property.2.1
  obtain ⟨left, _⟩ := graphBall_exists_walk_length_le Go root l ell hl
  have hedge : Go.Adj l (φ.symm ce).val := e.property.1
  have hcex : (deletedNeighborhoodCoverGraph G o i j ell r hi hj).Reachable ce x :=
    SimpleGraph.ConnectedComponent.exact (he.trans hx.symm)
  obtain ⟨p⟩ := hcex
  let toGo := (SimpleGraph.Embedding.induce (G := Go)
    (deletionNeighborhoodInnerSet G o i j ell r)ᶜ).toHom
  let right := (p.map φ.symm.toHom).map toGo
  have hreach : Go.Reachable root (φ.symm x).val :=
    (left.concat hedge).reachable.trans right.reachable
  have hfinite := SimpleGraph.edist_ne_top_iff_reachable.mpr hreach
  have hcoe : ((Go.dist root (φ.symm x).val : ℕ) : ℕ∞) = Go.edist root (φ.symm x).val :=
    ENat.coe_toNat hfinite
  have hcap := deletionNeighborhood_distance_bound G o i j ell r root (φ.symm x).val
  let f := (SimpleGraph.Embedding.induce (G := G) (deletionNeighborhoodVertices G o i j ell r)).toHom
  have hdist := graphHom_edist_le f root (φ.symm x).val
  change G.edist o x.val.val ≤ Go.edist root (φ.symm x).val at hdist
  exact hdist.trans (hcoe.symm.le.trans (ENat.coe_le_coe.mpr (hcap.trans hmargin)))

section Finite
variable [Fintype V]

/-- Actual boundary labels in one deleted covering component occupy a single
annulus fiber, so their count is paid by the original root-ball excess. -/
theorem deletedNeighborhoodCover_boundary_root_count (G : SimpleGraph V) (o i j : V)
    (ell r R ω : ℕ) (hr : 1 ≤ r)
    (hi : i ∉ graphBallVertices G o ell) (hj : j ∉ graphBallVertices G o ell)
    (hmargin : 6 * (ell + r) + 2 ≤ R) (hbudget : graphBallExcess G o R ≤ ω)
    (c : (deletedNeighborhoodCoverGraph G o i j ell r hi hj).ConnectedComponent) :
    Nat.card {e : BoundaryOrientedEdge G (graphBallVertices G o ell) //
      deletedNeighborhoodCenterVertex G o i j ell r hi hj (Sum.inl e) ∈ c.supp} ≤ ω + 1 := by
  let E := {e : BoundaryOrientedEdge G (graphBallVertices G o ell) //
    deletedNeighborhoodCenterVertex G o i j ell r hi hj (Sum.inl e) ∈ c.supp}
  by_cases hnon : Nonempty E
  · let e0 := Classical.choice hnon
    let hR : ell + 1 ≤ R := by omega
    let C := ambientBoundaryComponent G o hR e0.val
    let H := deletedNeighborhoodCoverGraph G o i j ell r hi hj
    have houter (x : ballCoverVertices (outsideGraph G (graphBallVertices G o ell))
        (deletedNeighborhoodCoverCenter G o i j ell hi hj) (deletedNeighborhoodCoverRadius G o ell r))
        (hx : x ∈ c.supp) : x.val.val ∈ graphBallVertices G o R :=
      deletedNeighborhoodCover_component_outer G o i j ell r R hr hi hj hmargin c e0.val e0.property x hx
    let f : H.induce c.supp →g outsideGraph (graphBall G o R) (ballCutInner G o ell R) :=
      { toFun := fun x => ⟨⟨x.val.val.val, houter x.val x.property⟩, x.val.val.property⟩
        map_rel' := fun h => h }
    have hsame (e : E) : ambientBoundaryComponent G o hR e.val = C := by
      let a : c.supp := ⟨deletedNeighborhoodCenterVertex G o i j ell r hi hj (Sum.inl e0.val), e0.property⟩
      let b : c.supp := ⟨deletedNeighborhoodCenterVertex G o i j ell r hi hj (Sum.inl e.val), e.property⟩
      obtain ⟨p⟩ := c.connected_induce_supp a b
      have hh := SimpleGraph.ConnectedComponent.sound (p.map f).reachable
      exact hh.symm
    let enc : E → AmbientBallBoundaryFiber G o hR C := fun e => ⟨e.val, hsame e⟩
    have hinj : Function.Injective enc := by
      intro a b hh
      exact Subtype.ext (congrArg (fun v : AmbientBallBoundaryFiber G o hR C => v.val) hh)
    exact (Nat.card_le_card_of_injective enc hinj).trans
      (ambient_boundary_component_count_bound G o hR hbudget C)
  · letI : IsEmpty E := ⟨fun e => hnon ⟨e⟩⟩
    change Nat.card E ≤ _
    simp

/-- The two target centers add at most two labels to the actual boundary
attachment count. Repeated boundary endpoints remain separate labels. -/
theorem deletedNeighborhoodCover_root_count (G : SimpleGraph V) (o i j : V)
    (ell r R ω : ℕ) (hr : 1 ≤ r)
    (hi : i ∉ graphBallVertices G o ell) (hj : j ∉ graphBallVertices G o ell)
    (hmargin : 6 * (ell + r) + 2 ≤ R) (hbudget : graphBallExcess G o R ≤ ω)
    (c : (deletedNeighborhoodCoverGraph G o i j ell r hi hj).ConnectedComponent) :
    Nat.card {a : BoundaryOrientedEdge G (graphBallVertices G o ell) ⊕ Fin 2 //
      deletedNeighborhoodCenterVertex G o i j ell r hi hj a ∈ c.supp} ≤ ω + 3 := by
  let P := fun a : BoundaryOrientedEdge G (graphBallVertices G o ell) ⊕ Fin 2 =>
    deletedNeighborhoodCenterVertex G o i j ell r hi hj a ∈ c.supp
  have hsum := Nat.card_congr (Equiv.subtypeSum (p := P))
  rw [Nat.card_sum] at hsum
  have hboundary := deletedNeighborhoodCover_boundary_root_count G o i j ell r R ω hr hi hj hmargin hbudget c
  have htarget : Nat.card {a : Fin 2 // P (Sum.inr a)} ≤ 2 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using Nat.card_le_card_of_injective
      (Subtype.val : {a : Fin 2 // P (Sum.inr a)} → Fin 2) Subtype.val_injective
  change Nat.card {a // P a} ≤ _
  change Nat.card {e // P (Sum.inl e)} ≤ ω + 1 at hboundary
  omega

/-- The actual deleted finite model has diameter O_omega(r), independently
of the total boundary size and of the number of vertices of the model. -/
theorem deletedNeighborhood_distance_bound (G : SimpleGraph V) (o i j : V)
    (ell r R ω : ℕ) (hr : 1 ≤ r)
    (hi : i ∉ graphBallVertices G o ell) (hj : j ∉ graphBallVertices G o ell)
    (hmargin : 6 * (ell + r) + 2 ≤ R) (hbudget : graphBallExcess G o R ≤ ω)
    (a b : ((deletionNeighborhoodInnerSet G o i j ell r)ᶜ :
      Set (deletionNeighborhoodVertices G o i j ell r))) :
    (outsideGraph (deletionNeighborhoodGraph G o i j ell r)
      (deletionNeighborhoodInnerSet G o i j ell r)).dist a b ≤
        2 * r + (ω + 2) * (2 * r + 1) := by
  have hh := deletedNeighborhood_distance_bound_of_root_count G o i j ell r hr hi hj (ω + 3)
    (deletedNeighborhoodCover_root_count G o i j ell r R ω hr hi hj hmargin hbudget) a b
  simpa only [show ω + 3 - 1 = ω + 2 by omega] using hh

end Finite
end LocalLaw
