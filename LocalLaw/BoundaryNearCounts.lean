import LocalLaw.LocalExcessGeometry

/-!
# Actual nearby boundary counts after removing a graph ball

Short exterior walks stay in the actual outer annulus under the literal
finite-radius margin ell+1+h<=R. This turns the proved cutset component
multiplicities into the two geometric counts of Proposition 5.2.
-/

open scoped BigOperators
set_option maxHeartbeats 200000

namespace LocalLaw
noncomputable section
local instance boundaryNearDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*}

/-- The actual outside endpoint of an oriented boundary edge. -/
def boundaryOuterEndpoint (G : SimpleGraph V) (T : Set V) (e : BoundaryOrientedEdge G T) :
    {v : V // v ∉ T} := ⟨e.val.2, e.property.2.2⟩

/-- The same outside vertex inside the actual nested-ball annulus. -/
def annulusOuterVertex (G : SimpleGraph V) (o : V) (ell R : ℕ)
    (x : {v : V // v ∉ graphBallVertices G o ell}) (hx : x.val ∈ graphBallVertices G o R) :
    {v : graphBallVertices G o R // v ∉ ballCutInner G o ell R} :=
  ⟨⟨x.val, hx⟩, x.property⟩

/-- A walk all of whose vertices stay in the outer ball genuinely lifts to
the induced annulus, preserving its exact length. -/
theorem exterior_walk_lift_annulus (G : SimpleGraph V) (o : V) (ell R : ℕ)
    {a b : {v : V // v ∉ graphBallVertices G o ell}}
    (p : (outsideGraph G (graphBallVertices G o ell)).Walk a b)
    (hsupp : ∀ x ∈ p.support, x.val ∈ graphBallVertices G o R)
    (ha : a.val ∈ graphBallVertices G o R) (hb : b.val ∈ graphBallVertices G o R) :
    ∃ q : (outsideGraph (graphBall G o R) (ballCutInner G o ell R)).Walk
      (annulusOuterVertex G o ell R a ha) (annulusOuterVertex G o ell R b hb), q.length = p.length := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons a c b hac p ih =>
    have hc : c.val ∈ graphBallVertices G o R := hsupp c (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr p.start_mem_support)
    have htail : ∀ x ∈ p.support, x.val ∈ graphBallVertices G o R := by
      intro x hx
      exact hsupp x (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr hx)
    obtain ⟨q, hq⟩ := ih htail hc hb
    have hadj : (outsideGraph (graphBall G o R) (ballCutInner G o ell R)).Adj
        (annulusOuterVertex G o ell R a ha) (annulusOuterVertex G o ell R c hc) := hac
    exact ⟨q.cons hadj, by simp only [SimpleGraph.Walk.length_cons, hq]⟩

/-- Every point of a short exterior walk from an inner-boundary endpoint
lies in the actual outer ball. -/
theorem boundary_short_walk_support (G : SimpleGraph V) (o : V) (ell R h : ℕ)
    (hmargin : ell + 1 + h ≤ R) (e : BoundaryOrientedEdge G (graphBallVertices G o ell))
    {b : {v : V // v ∉ graphBallVertices G o ell}}
    (p : (outsideGraph G (graphBallVertices G o ell)).Walk (boundaryOuterEndpoint G _ e) b)
    (hlen : p.length ≤ h) : ∀ x ∈ p.support, x.val ∈ graphBallVertices G o R := by
  classical
  intro x hx
  let f := (SimpleGraph.Embedding.induce (G := G) (graphBallVertices G o ell)ᶜ).toHom
  have hpref := SimpleGraph.edist_le ((p.takeUntil x hx).map f)
  have hprefix : G.edist e.val.2 x.val ≤ (h : ℕ∞) := by
    exact hpref.trans (by
      simp only [SimpleGraph.Walk.length_map]
      exact ENat.coe_le_coe.mpr ((p.length_takeUntil_le hx).trans hlen))
  have ha : e.val.2 ∈ graphBallVertices G o (ell + 1) :=
    adjacent_inner_mem_outer_ball G o le_rfl e.property.2.1 e.property.1
  calc
    G.edist o x.val ≤ G.edist o e.val.2 + G.edist e.val.2 x.val := G.edist_triangle
    _ ≤ ((ell + 1 : ℕ) : ℕ∞) + (h : ℕ∞) := add_le_add ha hprefix
    _ = ((ell + 1 + h : ℕ) : ℕ∞) := by simp only [Nat.cast_add]
    _ ≤ (R : ℕ∞) := ENat.coe_le_coe.mpr hmargin

/-- A nearby outside vertex belongs to the annulus and to the same actual
annulus component as the boundary endpoint. -/
theorem boundary_near_annulus_component (G : SimpleGraph V) (o : V) (ell R h : ℕ)
    (hmargin : ell + 1 + h ≤ R)
    (e : BoundaryOrientedEdge G (graphBallVertices G o ell))
    (x : {v : V // v ∉ graphBallVertices G o ell})
    (hnear : (outsideGraph G (graphBallVertices G o ell)).edist (boundaryOuterEndpoint G _ e) x ≤ (h : ℕ∞)) :
    ∃ hx : x.val ∈ graphBallVertices G o R,
      ambientBoundaryComponent G o (show ell + 1 ≤ R by omega) e =
        (outsideGraph (graphBall G o R) (ballCutInner G o ell R)).connectedComponentMk
          (annulusOuterVertex G o ell R x hx) := by
  have hfinite := ne_top_of_le_ne_top (ENat.coe_ne_top h) hnear
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfinite
  have hlen : p.length ≤ h := ENat.coe_le_coe.mp (hp.trans_le hnear)
  have hsupp := boundary_short_walk_support G o ell R h hmargin e p hlen
  have hx := hsupp x p.end_mem_support
  have ha := hsupp _ p.start_mem_support
  obtain ⟨q, _⟩ := exterior_walk_lift_annulus G o ell R p hsupp ha hx
  refine ⟨hx, ?_⟩
  exact SimpleGraph.ConnectedComponent.sound q.reachable

/-- Two sufficiently nearby boundary labels lie in the same actual annulus
component. Labels may share an outside vertex and are still counted separately. -/
theorem nearby_boundary_same_component (G : SimpleGraph V) (o : V) (ell R h : ℕ)
    (hmargin : ell + 1 + h ≤ R)
    (e f : BoundaryOrientedEdge G (graphBallVertices G o ell))
    (hnear : (outsideGraph G (graphBallVertices G o ell)).edist
      (boundaryOuterEndpoint G _ e) (boundaryOuterEndpoint G _ f) ≤ (h : ℕ∞)) :
    ambientBoundaryComponent G o (show ell + 1 ≤ R by omega) e =
      ambientBoundaryComponent G o (show ell + 1 ≤ R by omega) f := by
  obtain ⟨hx, hh⟩ := boundary_near_annulus_component G o ell R h hmargin e _ hnear
  exact hh

section FiniteCounts
variable [Fintype V] [DecidableEq V]

/-- Boundary labels which have another nearby boundary label in G(T). -/
def boundaryCollisionIndices (G : SimpleGraph V) (o : V) (ell h : ℕ) :
    Finset (BoundaryOrientedEdge G (graphBallVertices G o ell)) :=
  Finset.univ.filter (fun e => ∃ f : BoundaryOrientedEdge G (graphBallVertices G o ell), f ≠ e ∧
    (outsideGraph G (graphBallVertices G o ell)).edist (boundaryOuterEndpoint G _ e) (boundaryOuterEndpoint G _ f) ≤ (h : ℕ∞))

/-- Boundary labels close to an arbitrary actual outside vertex. -/
def nearbyBoundaryIndices (G : SimpleGraph V) (o : V) (ell h : ℕ)
    (x : {v : V // v ∉ graphBallVertices G o ell}) :
    Finset (BoundaryOrientedEdge G (graphBallVertices G o ell)) :=
  Finset.univ.filter (fun e => (outsideGraph G (graphBallVertices G o ell)).edist x (boundaryOuterEndpoint G _ e) ≤ (h : ℕ∞))

omit [DecidableEq V] in
/-- Nat.card of the actual annulus fiber equals its literal finite filter. -/
theorem ambientBoundaryFiber_card_filter (G : SimpleGraph V) (o : V) {ell R : ℕ}
    (h : ell + 1 ≤ R) (C : BallAnnulusComponent G o ell R) :
    Nat.card (AmbientBallBoundaryFiber G o h C) =
      (Finset.univ.filter (fun e => ambientBoundaryComponent G o h e = C)).card := by
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_subtype _

/-- Proposition 5.2's first actual boundary-label count, under an exact
finite-radius containment margin. Multiple labels at one vertex are retained. -/
theorem boundary_collision_count (G : SimpleGraph V) (o : V) (ell R h ω : ℕ)
    (hmargin : ell + 1 + h ≤ R) (hbudget : graphBallExcess G o R ≤ ω) :
    (boundaryCollisionIndices G o ell h).card ≤ 2 * ω := by
  let hR : ell + 1 ≤ R := by omega
  let F := ambientBoundaryComponent G o hR
  let goodComponents := (Finset.univ : Finset (BallAnnulusComponent G o ell R)).filter
    (fun C => 2 ≤ Nat.card (AmbientBallBoundaryFiber G o hR C))
  have hmaps : Set.MapsTo F (boundaryCollisionIndices G o ell h) goodComponents := by
    intro e he
    obtain ⟨f, hfe, hnear⟩ := (Finset.mem_filter.mp he).2
    have heq : F f = F e := (nearby_boundary_same_component G o ell R h hmargin e f hnear).symm
    have hpair : {e, f} ⊆ Finset.univ.filter (fun a => F a = F e) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
    have htwo : 2 ≤ Nat.card (AmbientBallBoundaryFiber G o hR (F e)) := by
      rw [ambientBoundaryFiber_card_filter]
      calc
        2 = ({e, f} : Finset (BoundaryOrientedEdge G (graphBallVertices G o ell))).card := (Finset.card_pair (Ne.symm hfe)).symm
        _ ≤ _ := Finset.card_le_card hpair
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htwo⟩
  have hcount := Finset.card_eq_sum_card_fiberwise
    (f := F) (s := boundaryCollisionIndices G o ell h) (t := goodComponents) hmaps
  calc
    _ = ∑ C ∈ goodComponents, ((boundaryCollisionIndices G o ell h).filter (fun e => F e = C)).card := by
      exact hcount
    _ ≤ ∑ C ∈ goodComponents, Nat.card (AmbientBallBoundaryFiber G o hR C) := by
      apply Finset.sum_le_sum
      intro C _
      rw [ambientBoundaryFiber_card_filter G o hR C]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
    _ ≤ 2 * ω := by
      have hh := ambient_boundary_multiple_attachment_bound G o hR hbudget
      dsimp only [goodComponents]
      simp only [Finset.sum_filter, ← finsum_eq_sum_of_fintype] at hh ⊢
      exact hh

omit [DecidableEq V] in
/-- Proposition 5.2's second actual count: any outside vertex is close to at
most omega+1 boundary labels. Annulus membership is derived if the set is nonempty. -/
theorem nearby_boundary_count (G : SimpleGraph V) (o : V) (ell R h ω : ℕ)
    (hmargin : ell + 1 + h ≤ R) (hbudget : graphBallExcess G o R ≤ ω)
    (x : {v : V // v ∉ graphBallVertices G o ell}) :
    (nearbyBoundaryIndices G o ell h x).card ≤ ω + 1 := by
  let hR : ell + 1 ≤ R := by omega
  by_cases hnon : (nearbyBoundaryIndices G o ell h x).Nonempty
  · obtain ⟨e, he⟩ := hnon
    have hnear := (Finset.mem_filter.mp he).2
    rw [(outsideGraph G (graphBallVertices G o ell)).edist_comm] at hnear
    obtain ⟨hx, _⟩ := boundary_near_annulus_component G o ell R h hmargin e x hnear
    let C := (outsideGraph (graphBall G o R) (ballCutInner G o ell R)).connectedComponentMk
      (annulusOuterVertex G o ell R x hx)
    have hsubset : nearbyBoundaryIndices G o ell h x ⊆
        Finset.univ.filter (fun f => ambientBoundaryComponent G o hR f = C) := by
      intro f hf
      have hnear := (Finset.mem_filter.mp hf).2
      rw [(outsideGraph G (graphBallVertices G o ell)).edist_comm] at hnear
      obtain ⟨hx', hh⟩ := boundary_near_annulus_component G o ell R h hmargin f x hnear
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩
    calc
      _ ≤ (Finset.univ.filter (fun f => ambientBoundaryComponent G o hR f = C)).card := Finset.card_le_card hsubset
      _ = Nat.card (AmbientBallBoundaryFiber G o hR C) := (ambientBoundaryFiber_card_filter G o hR C).symm
      _ ≤ ω + 1 := ambient_boundary_component_count_bound G o hR hbudget C
  · rw [Finset.not_nonempty_iff_eq_empty.mp hnon, Finset.card_empty]
    exact Nat.zero_le _

/-- Rounded half-radius specialization, with the necessary one-edge margin
made literal. The source logarithmic radius hierarchy implies this margin. -/
theorem boundary_half_radius_counts (G : SimpleGraph V) (o : V) (ell R ω : ℕ)
    (hmargin : 2 * ell + 2 ≤ R) (hbudget : graphBallExcess G o R ≤ ω) :
    (boundaryCollisionIndices G o ell (R / 2)).card ≤ 2 * ω ∧
      ∀ x : {v : V // v ∉ graphBallVertices G o ell},
        (nearbyBoundaryIndices G o ell (R / 2) x).card ≤ ω + 1 := by
  have hfit : ell + 1 + R / 2 ≤ R := by omega
  exact ⟨boundary_collision_count G o ell R (R / 2) ω hfit hbudget,
    nearby_boundary_count G o ell R (R / 2) ω hfit hbudget⟩

end FiniteCounts

end
end LocalLaw
