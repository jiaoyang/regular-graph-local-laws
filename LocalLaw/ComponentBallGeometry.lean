import LocalLaw.ComponentModel

/-!
# Actual graph balls inside isolated components

Graph homomorphisms contract extended distance, isolated restrictions preserve
it, and the ball around an isolated root is exactly the ambient ball. The
same actual restriction commutes with deletion, including intrinsic distances
after removal of the ball.
-/

noncomputable section
namespace LocalLaw
local instance componentBallDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Metrics
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem graphHom_edist_le (f : G →g H) (a b : V) :
    H.edist (f a) (f b) ≤ G.edist a b := by
  by_cases hr : G.Reachable a b
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
    have hh := SimpleGraph.edist_le (p.map f)
    simpa only [SimpleGraph.Walk.length_map, hp] using hh
  · rw [SimpleGraph.edist_eq_top_of_not_reachable hr]
    exact le_top

/-- Actual graph isomorphisms preserve extended distance, without any
connectedness hypothesis or natural-distance convention. -/
theorem graphIso_edist (e : G ≃g H) (a b : V) :
    H.edist (e a) (e b) = G.edist a b := by
  apply le_antisymm (graphHom_edist_le e.toHom a b)
  have hh := graphHom_edist_le e.symm.toHom (e a) (e b)
  change G.edist (e.symm (e a)) (e.symm (e b)) ≤ H.edist (e a) (e b) at hh
  simpa only [e.symm_apply_apply] using hh

theorem graphIso_dist (e : G ≃g H) (a b : V) :
    H.dist (e a) (e b) = G.dist a b := congrArg ENat.toNat (graphIso_edist e a b)

end Metrics

section Isolated
variable {V : Type*} (G : SimpleGraph V) (S : Set V)
    (hcut : ∀ i ∈ S, ∀ j ∉ S, ¬G.Adj i j)
include hcut

theorem walk_end_mem_isolated {a b : V} (p : G.Walk a b) (ha : a ∈ S) : b ∈ S := by
  induction p with
  | nil => exact ha
  | @cons a c b hac p ih =>
    apply ih
    by_contra hc
    exact hcut a ha c hc hac

theorem isolated_induce_edist (a b : S) :
    (G.induce S).edist a b = G.edist a.val b.val := by
  apply le_antisymm
  · by_cases hr : G.Reachable a.val b.val
    · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
      obtain ⟨q, hq⟩ := walk_restrict_isolated G S hcut p a.property b.property
      calc
        _ ≤ (q.length : ℕ∞) := SimpleGraph.edist_le q
        _ = (p.length : ℕ∞) := congrArg (fun n : ℕ => (n : ℕ∞)) hq
        _ = _ := hp
    · rw [SimpleGraph.edist_eq_top_of_not_reachable hr]
      exact le_top
  · exact graphHom_edist_le (SimpleGraph.Embedding.induce S).toHom a b

theorem isolated_graphBall_mem (root : S) (r : ℕ) (v : S) :
    v ∈ graphBallVertices (G.induce S) root r ↔ v.val ∈ graphBallVertices G root.val r := by
  change (G.induce S).edist root v ≤ (r : ℕ∞) ↔ G.edist root.val v.val ≤ (r : ℕ∞)
  rw [isolated_induce_edist G S hcut]

theorem isolated_ball_image (root : S) (r : ℕ) :
    (Subtype.val : S → V) '' graphBallVertices (G.induce S) root r =
      graphBallVertices G root.val r := by
  ext v
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (isolated_graphBall_mem G S hcut root r v).mp hv
  · intro hv
    have hfinite : G.edist root.val v ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top r) hv
    obtain ⟨p⟩ := SimpleGraph.reachable_of_edist_ne_top hfinite
    have hS := walk_end_mem_isolated G S hcut p root.property
    exact ⟨⟨v, hS⟩, (isolated_graphBall_mem G S hcut root r ⟨v, hS⟩).mpr hv, rfl⟩

def isolatedBallEquiv (root : S) (r : ℕ) :
    graphBallVertices (G.induce S) root r ≃ graphBallVertices G root.val r :=
  (Equiv.Set.image (Subtype.val : S → V) _ Subtype.val_injective).trans
    (Equiv.setCongr (isolated_ball_image G S hcut root r))

@[simp] theorem isolatedBallEquiv_val (root : S) (r : ℕ)
    (v : graphBallVertices (G.induce S) root r) :
    (isolatedBallEquiv G S hcut root r v).val = v.val.val := rfl

/-- Deleting the root ball commutes with an actual isolated restriction. -/
def isolatedBallDeletionIso (root : S) (r : ℕ) :
    (outsideGraph (G.induce S) (graphBallVertices (G.induce S) root r)) ≃g
      ((outsideGraph G (graphBallVertices G root.val r)).induce
        {v : ((graphBallVertices G root.val r)ᶜ : Set V) | v.val ∈ S}) where
  toFun v := ⟨⟨v.val.val, fun hh => v.property
    ((isolated_graphBall_mem G S hcut root r v.val).mpr hh)⟩, v.val.property⟩
  invFun v := ⟨⟨v.val.val, v.property⟩, fun hh => v.val.property
    ((isolated_graphBall_mem G S hcut root r ⟨v.val.val, v.property⟩).mp hh)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isolated_graphBall_deleted_distance (root : S) (r : ℕ)
    (a b : ((graphBallVertices (G.induce S) root r)ᶜ : Set S)) :
    (outsideGraph (G.induce S) (graphBallVertices (G.induce S) root r)).dist a b =
      (outsideGraph G (graphBallVertices G root.val r)).dist
        ((isolatedBallDeletionIso G S hcut root r) a).val
        ((isolatedBallDeletionIso G S hcut root r) b).val := by
  have hh := graphIso_dist (isolatedBallDeletionIso G S hcut root r) a b
  have hdist := isolated_induce_distance (outsideGraph G (graphBallVertices G root.val r))
    {v : ((graphBallVertices G root.val r)ᶜ : Set V) | v.val ∈ S}
    (by intro i hi j hj hij; exact hcut i.val hi j.val hj hij)
    ((isolatedBallDeletionIso G S hcut root r) a) ((isolatedBallDeletionIso G S hcut root r) b)
  exact hh.symm.trans hdist

end Isolated

section DeleteRestriction
variable {V : Type*} (G : SimpleGraph V) (S T : Set V)

/-- Actual nested restriction and deletion differ only by swapping the two
membership proofs; their adjacency relations are identical. -/
def deletionRestrictionIso :
    ((G.induce S).induce {v : S | v.val ∉ T}) ≃g
      ((outsideGraph G T).induce {v : (Tᶜ : Set V) | v.val ∈ S}) where
  toFun v := ⟨⟨v.val.val, v.property⟩, v.val.property⟩
  invFun v := ⟨⟨v.val.val, v.property⟩, v.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem deleted_restriction_distance
    (hcut : ∀ i ∈ S, ∀ j ∉ S, ¬G.Adj i j)
    (a b : {v : S // v.val ∉ T}) :
    ((G.induce S).induce {v : S | v.val ∉ T}).dist a b =
      (outsideGraph G T).dist ⟨a.val.val, a.property⟩ ⟨b.val.val, b.property⟩ := by
  have hh := graphIso_dist (deletionRestrictionIso G S T) a b
  have hdist := isolated_induce_distance (outsideGraph G T) {v : (Tᶜ : Set V) | v.val ∈ S}
    (by intro i hi j hj hij; exact hcut i.val hi j.val hj hij)
    ((deletionRestrictionIso G S T) a) ((deletionRestrictionIso G S T) b)
  exact hh.symm.trans hdist

end DeleteRestriction
end LocalLaw
