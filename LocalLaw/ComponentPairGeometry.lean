import LocalLaw.ComponentBallGeometry
import LocalLaw.PairBallGeometry

/-!
# Pair neighborhoods inside actual components

An isolated restriction preserves both endpoint balls and their union.
Disconnected pair neighborhoods have no path between their distinguished
endpoints; a short ambient path would lift into the union and contradict it.
-/

noncomputable section
namespace LocalLaw
local instance componentPairDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

theorem walk_lift_induced_of_support (G : SimpleGraph V) (S : Set V) {a b : V}
    (p : G.Walk a b) (hsupp : ∀ v ∈ p.support, v ∈ S) (ha : a ∈ S) (hb : b ∈ S) :
    ∃ q : (G.induce S).Walk ⟨a, ha⟩ ⟨b, hb⟩, q.length = p.length := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons a c b hac p ih =>
    have hc : c ∈ S := hsupp c (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr p.start_mem_support)
    have htail : ∀ v ∈ p.support, v ∈ S := by
      intro v hv
      exact hsupp v (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr hv)
    obtain ⟨q, hq⟩ := ih htail hc hb
    exact ⟨q.cons (show (G.induce S).Adj ⟨a, ha⟩ ⟨c, hc⟩ from hac),
      by simp only [SimpleGraph.Walk.length_cons, hq]⟩

theorem pairBall_connected_of_reachable_endpoints (G : SimpleGraph V) (i j : V) (r : ℕ)
    (hij : (pairBallGraph G i j r).Reachable (pairBallLeft G i j r) (pairBallRight G i j r)) :
    (pairBallGraph G i j r).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨pairBallLeft G i j r, ?_⟩
  intro v
  rcases v.property with hv | hv
  · obtain ⟨p, _⟩ := pairBall_left_walk_bound G i j r (pairBallLeft G i j r) v
      (center_mem_graphBall G i r) hv
    exact p.reachable
  · obtain ⟨p, _⟩ := pairBall_right_walk_bound G i j r (pairBallRight G i j r) v
      (center_mem_graphBall G j r) hv
    exact hij.trans p.reachable

theorem pairBall_endpoint_not_reachable (G : SimpleGraph V) (i j : V) (r : ℕ)
    (h : ¬(pairBallGraph G i j r).Connected) :
    ¬(pairBallGraph G i j r).Reachable (pairBallLeft G i j r) (pairBallRight G i j r) :=
  fun hh => h (pairBall_connected_of_reachable_endpoints G i j r hh)

theorem pairBall_disconnected_distance_lower (G : SimpleGraph V) (i j : V) (r : ℕ)
    (hreach : G.Reachable i j) (h : ¬(pairBallGraph G i j r).Connected) :
    2 * r + 1 < G.dist i j := by
  by_contra hn
  obtain ⟨p, _, hp⟩ := hreach.exists_path_of_dist
  have hlen : p.length ≤ 2 * r + 1 := by omega
  obtain ⟨q, _⟩ := walk_lift_induced_of_support G (pairBallVertices G i j r) p
    (walk_support_pairBall G i j r p hlen) (pairBallLeft G i j r).property (pairBallRight G i j r).property
  exact pairBall_endpoint_not_reachable G i j r h q.reachable

section Isolated
variable (G : SimpleGraph V) (S : Set V)
    (hcut : ∀ i ∈ S, ∀ j ∉ S, ¬G.Adj i j)
include hcut

theorem isolated_pairBall_image (i j : S) (r : ℕ) :
    (Subtype.val : S → V) '' pairBallVertices (G.induce S) i j r =
      pairBallVertices G i.val j.val r := by
  change (Subtype.val : S → V) '' (graphBallVertices (G.induce S) i r ∪
    graphBallVertices (G.induce S) j r) = graphBallVertices G i.val r ∪ graphBallVertices G j.val r
  rw [Set.image_union, isolated_ball_image G S hcut i r, isolated_ball_image G S hcut j r]

def isolatedPairBallEquiv (i j : S) (r : ℕ) :
    pairBallVertices (G.induce S) i j r ≃ pairBallVertices G i.val j.val r :=
  (Equiv.Set.image (Subtype.val : S → V) _ Subtype.val_injective).trans
    (Equiv.setCongr (isolated_pairBall_image G S hcut i j r))

def isolatedPairBallIso (i j : S) (r : ℕ) :
    pairBallGraph (G.induce S) i j r ≃g pairBallGraph G i.val j.val r where
  toEquiv := isolatedPairBallEquiv G S hcut i j r
  map_rel_iff' := Iff.rfl

@[simp] theorem isolatedPairBallIso_val (i j : S) (r : ℕ)
    (v : pairBallVertices (G.induce S) i j r) :
    (isolatedPairBallIso G S hcut i j r v).val = v.val.val := rfl

@[simp] theorem isolatedPairBallIso_left (i j : S) (r : ℕ) :
    isolatedPairBallIso G S hcut i j r (pairBallLeft (G.induce S) i j r) =
      pairBallLeft G i.val j.val r := rfl

@[simp] theorem isolatedPairBallIso_right (i j : S) (r : ℕ) :
    isolatedPairBallIso G S hcut i j r (pairBallRight (G.induce S) i j r) =
      pairBallRight G i.val j.val r := rfl

end Isolated
end LocalLaw
