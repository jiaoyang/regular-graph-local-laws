import LocalLaw.NeighborhoodDeletionModel
import LocalLaw.BoundaryNearCounts

/-!
# The actual boundary-ball cover after deleting the inner root ball

A walk either remains outside the removed set or has a last exit through an
actual oriented boundary edge. Recording the prefix and suffix lengths gives
the precise radius r-1 for boundary centers and radius r for the two targets.
-/

noncomputable section
namespace LocalLaw
local instance deletedNeighborhoodCoverDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

/-- An exact last-exit decomposition. The outside suffix is a genuine walk
in the induced complement and the removed-edge length is counted once. -/
theorem walk_outside_or_last_exit (G : SimpleGraph V) (T : Set V) {a b : V}
    (p : G.Walk a b) (hb : b ∉ T) :
    (∃ ha : a ∉ T, ∃ q : (outsideGraph G T).Walk ⟨a, ha⟩ ⟨b, hb⟩, q.length = p.length) ∨
    ∃ e : BoundaryOrientedEdge G T, ∃ pref : G.Walk a e.val.1,
      ∃ q : (outsideGraph G T).Walk (boundaryOuterEndpoint G T e) ⟨b, hb⟩,
        pref.length + 1 + q.length = p.length := by
  induction p with
  | nil => exact Or.inl ⟨hb, SimpleGraph.Walk.nil, rfl⟩
  | @cons a c b hac p ih =>
    rcases ih hb with ⟨hc, q, hq⟩ | ⟨e, pref, q, hlen⟩
    · by_cases ha : a ∈ T
      · right
        refine ⟨⟨(a, c), hac, ha, hc⟩, SimpleGraph.Walk.nil, q, ?_⟩
        simp only [SimpleGraph.Walk.length_nil, SimpleGraph.Walk.length_cons, hq]
        omega
      · left
        have hac' : (outsideGraph G T).Adj ⟨a, ha⟩ ⟨c, hc⟩ := hac
        exact ⟨ha, q.cons hac', by simp only [SimpleGraph.Walk.length_cons, hq]⟩
    · right
      refine ⟨e, pref.cons hac, q, ?_⟩
      simp only [SimpleGraph.Walk.length_cons]
      omega

theorem graphBall_exists_walk_length_le (G : SimpleGraph V) (o v : V) (r : ℕ)
    (hv : v ∈ graphBallVertices G o r) : ∃ p : G.Walk o v, p.length ≤ r := by
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
    (ne_top_of_le_ne_top (ENat.coe_ne_top r) hv)
  exact ⟨p, ENat.coe_le_coe.mp (hp.trans_le hv)⟩

/-- Outside points of the expanded root ball are within r-1 of an actual
boundary endpoint in the deleted graph. -/
theorem expanded_root_ball_outside_tail (G : SimpleGraph V) (o v : V) (ell r : ℕ)
    (hvout : v ∉ graphBallVertices G o ell)
    (hv : v ∈ graphBallVertices G o (ell + r)) :
    ∃ e : BoundaryOrientedEdge G (graphBallVertices G o ell),
      ∃ q : (outsideGraph G (graphBallVertices G o ell)).Walk
        (boundaryOuterEndpoint G _ e) ⟨v, hvout⟩, q.length + 1 ≤ r := by
  obtain ⟨p, hp⟩ := graphBall_exists_walk_length_le G o v (ell + r) hv
  rcases walk_outside_or_last_exit G (graphBallVertices G o ell) p hvout with
    ⟨ho, _, _⟩ | ⟨e, pref, q, hlen⟩
  · exact False.elim (ho (center_mem_graphBall G o ell))
  · have hpref : ell ≤ pref.length := by
      by_contra hn
      have hshort : pref.length + 1 ≤ ell := by omega
      have hh := SimpleGraph.edist_le (pref.concat e.property.1)
      have houtside : e.val.2 ∈ graphBallVertices G o ell := hh.trans (by
        simpa only [SimpleGraph.Walk.length_concat] using ENat.coe_le_coe.mpr hshort)
      exact e.property.2.2 houtside
    exact ⟨e, q, by omega⟩

/-- An expanded target ball is covered either from its outside target or
from a last boundary exit, with the exact corresponding radius. -/
theorem target_ball_outside_tail (G : SimpleGraph V) (T : Set V) (i v : V) (r : ℕ)
    (hi : i ∉ T) (hvout : v ∉ T) (hv : v ∈ graphBallVertices G i r) :
    (∃ q : (outsideGraph G T).Walk ⟨i, hi⟩ ⟨v, hvout⟩, q.length ≤ r) ∨
      ∃ e : BoundaryOrientedEdge G T,
        ∃ q : (outsideGraph G T).Walk (boundaryOuterEndpoint G T e) ⟨v, hvout⟩,
          q.length + 1 ≤ r := by
  obtain ⟨p, hp⟩ := graphBall_exists_walk_length_le G i v r hv
  rcases walk_outside_or_last_exit G T p hvout with ⟨_, q, hq⟩ | ⟨e, pref, q, hlen⟩
  · exact Or.inl ⟨q, hq.trans_le hp⟩
  · exact Or.inr ⟨e, q, by omega⟩

def deletedNeighborhoodCoverCenter (G : SimpleGraph V) (o i j : V) (ell : ℕ)
    (hi : i ∉ graphBallVertices G o ell) (hj : j ∉ graphBallVertices G o ell) :
    BoundaryOrientedEdge G (graphBallVertices G o ell) ⊕ Fin 2 →
      ((graphBallVertices G o ell)ᶜ : Set V)
  | Sum.inl e => boundaryOuterEndpoint G _ e
  | Sum.inr a => Fin.cases ⟨i, hi⟩ (fun _ => ⟨j, hj⟩) a

def deletedNeighborhoodCoverRadius (G : SimpleGraph V) (o : V) (ell r : ℕ) :
    BoundaryOrientedEdge G (graphBallVertices G o ell) ⊕ Fin 2 → ℕ
  | Sum.inl _ => r - 1
  | Sum.inr _ => r

abbrev deletedNeighborhoodCoverGraph (G : SimpleGraph V) (o i j : V) (ell r : ℕ)
    (hi : i ∉ graphBallVertices G o ell) (hj : j ∉ graphBallVertices G o ell) :=
  ballCoverGraph (outsideGraph G (graphBallVertices G o ell))
    (deletedNeighborhoodCoverCenter G o i j ell hi hj) (deletedNeighborhoodCoverRadius G o ell r)

def deletedNeighborhoodCenterVertex (G : SimpleGraph V) (o i j : V) (ell r : ℕ)
    (hi : i ∉ graphBallVertices G o ell) (hj : j ∉ graphBallVertices G o ell)
    (a : BoundaryOrientedEdge G (graphBallVertices G o ell) ⊕ Fin 2) :
    ballCoverVertices (outsideGraph G (graphBallVertices G o ell))
      (deletedNeighborhoodCoverCenter G o i j ell hi hj) (deletedNeighborhoodCoverRadius G o ell r) :=
  ballCoverCenter _ _ _ a

theorem deletedNeighborhoodCover_radius_le (G : SimpleGraph V) (o : V) (ell r : ℕ)
    (a : BoundaryOrientedEdge G (graphBallVertices G o ell) ⊕ Fin 2) :
    deletedNeighborhoodCoverRadius G o ell r a ≤ r := by
  cases a <;> simp only [deletedNeighborhoodCoverRadius]
  · exact Nat.sub_le _ _
  · exact le_rfl

/-- The deleted finite neighborhood is exactly the union of the boundary
balls of radius r-1 and the two outside target balls of radius r. -/
theorem deletedNeighborhoodCover_set (G : SimpleGraph V) (o i j : V) (ell r : ℕ)
    (hr : 1 ≤ r) (hi : i ∉ graphBallVertices G o ell) (hj : j ∉ graphBallVertices G o ell) :
    ballCoverVertices (outsideGraph G (graphBallVertices G o ell))
      (deletedNeighborhoodCoverCenter G o i j ell hi hj)
      (deletedNeighborhoodCoverRadius G o ell r) =
      {v : ((graphBallVertices G o ell)ᶜ : Set V) |
        v.val ∈ deletionNeighborhoodVertices G o i j ell r} := by
  let T := graphBallVertices G o ell
  let f := (SimpleGraph.Embedding.induce (G := G) Tᶜ).toHom
  ext v
  constructor
  · rintro ⟨a, ha⟩
    apply (mem_tripleBallVertices G o i j v.val (ell + r) r r).mpr
    cases a with
    | inl e =>
      left
      change (outsideGraph G T).edist (boundaryOuterEndpoint G T e) v ≤ ((r - 1 : ℕ) : ℕ∞) at ha
      have htail := (graphHom_edist_le f (boundaryOuterEndpoint G T e) v).trans ha
      have hhead : e.val.2 ∈ graphBallVertices G o (ell + 1) :=
        adjacent_inner_mem_outer_ball G o le_rfl e.property.2.1 e.property.1
      calc
        G.edist o v.val ≤ G.edist o e.val.2 + G.edist e.val.2 v.val := G.edist_triangle
        _ ≤ ((ell + 1 : ℕ) : ℕ∞) + ((r - 1 : ℕ) : ℕ∞) := add_le_add hhead htail
        _ = ((ell + r : ℕ) : ℕ∞) := by
          rw [← Nat.cast_add]
          congr 1
          omega
    | inr a =>
      fin_cases a
      · right; left
        change (outsideGraph G T).edist ⟨i, hi⟩ v ≤ (r : ℕ∞) at ha
        exact (graphHom_edist_le f ⟨i, hi⟩ v).trans ha
      · right; right
        change (outsideGraph G T).edist ⟨j, hj⟩ v ≤ (r : ℕ∞) at ha
        exact (graphHom_edist_le f ⟨j, hj⟩ v).trans ha
  · intro hv
    change v.val ∈ tripleBallVertices G o i j (ell + r) r r at hv
    rcases (mem_tripleBallVertices G o i j v.val (ell + r) r r).mp hv with hroot | hleft | hright
    · obtain ⟨e, q, hq⟩ := expanded_root_ball_outside_tail G o v.val ell r v.property hroot
      refine ⟨Sum.inl e, ?_⟩
      exact (SimpleGraph.edist_le q).trans (ENat.coe_le_coe.mpr (show q.length ≤ r - 1 by omega))
    · rcases target_ball_outside_tail G T i v.val r hi v.property hleft with ⟨q, hq⟩ | ⟨e, q, hq⟩
      · refine ⟨Sum.inr 0, ?_⟩
        exact (SimpleGraph.edist_le q).trans (ENat.coe_le_coe.mpr hq)
      · refine ⟨Sum.inl e, ?_⟩
        exact (SimpleGraph.edist_le q).trans (ENat.coe_le_coe.mpr (show q.length ≤ r - 1 by omega))
    · rcases target_ball_outside_tail G T j v.val r hj v.property hright with ⟨q, hq⟩ | ⟨e, q, hq⟩
      · refine ⟨Sum.inr 1, ?_⟩
        exact (SimpleGraph.edist_le q).trans (ENat.coe_le_coe.mpr hq)
      · refine ⟨Sum.inl e, ?_⟩
        exact (SimpleGraph.edist_le q).trans (ENat.coe_le_coe.mpr (show q.length ≤ r - 1 by omega))

def deletionNeighborhoodInnerSet (G : SimpleGraph V) (o i j : V) (ell r : ℕ) :
    Set (deletionNeighborhoodVertices G o i j ell r) :=
  graphBallVertices (deletionNeighborhoodGraph G o i j ell r)
    (deletionNeighborhoodRoot G o i j ell r) ell

theorem deletionNeighborhood_inner_mem (G : SimpleGraph V) (o i j : V) (ell r : ℕ)
    (v : deletionNeighborhoodVertices G o i j ell r) :
    v ∈ deletionNeighborhoodInnerSet G o i j ell r ↔ v.val ∈ graphBallVertices G o ell :=
  induced_root_ball_mem G _ o _ ell (deletionNeighborhood_contains_root_ball G o i j ell r) v

/-- The correctly deleted finite model is genuinely isomorphic to the
outside-graph boundary-ball cover; no distance identification is assumed. -/
def deletedNeighborhoodCoverIso (G : SimpleGraph V) (o i j : V) (ell r : ℕ)
    (hr : 1 ≤ r) (hi : i ∉ graphBallVertices G o ell) (hj : j ∉ graphBallVertices G o ell) :
    (outsideGraph (deletionNeighborhoodGraph G o i j ell r)
      (deletionNeighborhoodInnerSet G o i j ell r)) ≃g
    (ballCoverGraph (outsideGraph G (graphBallVertices G o ell))
      (deletedNeighborhoodCoverCenter G o i j ell hi hj)
      (deletedNeighborhoodCoverRadius G o ell r)) where
  toFun v := ⟨⟨v.val.val, fun hh => v.property
    ((deletionNeighborhood_inner_mem G o i j ell r v.val).mpr hh)⟩, by
      rw [deletedNeighborhoodCover_set G o i j ell r hr hi hj]
      exact v.val.property⟩
  invFun v := ⟨⟨v.val.val, by
      exact (Set.ext_iff.mp (deletedNeighborhoodCover_set G o i j ell r hr hi hj) v.val).mp v.property⟩, fun hh => v.val.property
        ((deletionNeighborhood_inner_mem G o i j ell r _).mp hh)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

section Finite
variable [Fintype V]

/-- Once actual component center counts are supplied, the genuine deleted
model inherits their linear radius diameter cap through the proved cover. -/
theorem deletedNeighborhood_distance_bound_of_root_count (G : SimpleGraph V) (o i j : V) (ell r : ℕ)
    (hr : 1 ≤ r) (hi : i ∉ graphBallVertices G o ell) (hj : j ∉ graphBallVertices G o ell)
    (κ : ℕ)
    (hroots : ∀ c : (ballCoverGraph (outsideGraph G (graphBallVertices G o ell))
      (deletedNeighborhoodCoverCenter G o i j ell hi hj)
      (deletedNeighborhoodCoverRadius G o ell r)).ConnectedComponent,
      Nat.card {a : BoundaryOrientedEdge G (graphBallVertices G o ell) ⊕ Fin 2 //
        ballCoverCenter (outsideGraph G (graphBallVertices G o ell))
          (deletedNeighborhoodCoverCenter G o i j ell hi hj)
          (deletedNeighborhoodCoverRadius G o ell r) a ∈ c.supp} ≤ κ)
    (a b : ((deletionNeighborhoodInnerSet G o i j ell r)ᶜ : Set (deletionNeighborhoodVertices G o i j ell r))) :
    (outsideGraph (deletionNeighborhoodGraph G o i j ell r)
      (deletionNeighborhoodInnerSet G o i j ell r)).dist a b ≤ 2 * r + (κ - 1) * (2 * r + 1) := by
  have hh := ballCover_distance_bound_of_component_root_count
    (outsideGraph G (graphBallVertices G o ell))
    (deletedNeighborhoodCoverCenter G o i j ell hi hj)
    (deletedNeighborhoodCoverRadius G o ell r) r
    (deletedNeighborhoodCover_radius_le G o ell r) κ hroots
    ((deletedNeighborhoodCoverIso G o i j ell r hr hi hj) a)
    ((deletedNeighborhoodCoverIso G o i j ell r hr hi hj) b)
  rw [graphIso_dist] at hh
  exact hh

end Finite

end LocalLaw
