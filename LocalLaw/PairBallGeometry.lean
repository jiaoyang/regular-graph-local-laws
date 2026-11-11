import LocalLaw.ComponentModel
import LocalLaw.TreeRadiusStability

/-!
# Intrinsic distances in the actual union of two balls

The two balls need not intersect. A reachable pair in their induced union can
be joined through one crossing edge, giving the true cap `4*r+1`. Unreachable
pairs have natural-valued graph distance zero.
-/

noncomputable section
namespace LocalLaw
local instance pairGeometryDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} (G : SimpleGraph V)

theorem walk_crosses_cut {a b : V} (p : G.Walk a b) (S : Set V)
    (ha : a ∈ S) (hb : b ∉ S) :
    ∃ x ∈ S, ∃ y ∉ S, G.Adj x y := by
  induction p with
  | nil => exact False.elim (hb ha)
  | @cons a c b hac p ih =>
    by_cases hc : c ∈ S
    · exact ih hc hb
    · exact ⟨a, ha, c, hc, hac⟩

theorem pairBall_left_walk_bound (i j : V) (r : ℕ)
    (a b : pairBallVertices G i j r)
    (ha : G.edist i a.val ≤ (r : ℕ∞)) (hb : G.edist i b.val ≤ (r : ℕ∞)) :
    ∃ p : (pairBallGraph G i j r).Walk a b, p.length ≤ 2 * r := by
  let aa : graphBallVertices G i r := ⟨a.val, ha⟩
  let bb : graphBallVertices G i r := ⟨b.val, hb⟩
  obtain ⟨p, hp⟩ := (graphBall_connected G i r).exists_walk_length_eq_dist aa bb
  let f : graphBall G i r →g pairBallGraph G i j r :=
    { toFun := fun v => ⟨v.val, Or.inl v.property⟩
      map_rel' := fun h => h }
  refine ⟨p.map f, ?_⟩
  simpa only [SimpleGraph.Walk.length_map, hp] using graphBall_distance_le_twice_radius G i r aa bb

theorem pairBall_right_walk_bound (i j : V) (r : ℕ)
    (a b : pairBallVertices G i j r)
    (ha : G.edist j a.val ≤ (r : ℕ∞)) (hb : G.edist j b.val ≤ (r : ℕ∞)) :
    ∃ p : (pairBallGraph G i j r).Walk a b, p.length ≤ 2 * r := by
  let aa : graphBallVertices G j r := ⟨a.val, ha⟩
  let bb : graphBallVertices G j r := ⟨b.val, hb⟩
  obtain ⟨p, hp⟩ := (graphBall_connected G j r).exists_walk_length_eq_dist aa bb
  let f : graphBall G j r →g pairBallGraph G i j r :=
    { toFun := fun v => ⟨v.val, Or.inr v.property⟩
      map_rel' := fun h => h }
  refine ⟨p.map f, ?_⟩
  simpa only [SimpleGraph.Walk.length_map, hp] using graphBall_distance_le_twice_radius G j r aa bb

theorem pairBall_walk_bound_of_left (i j : V) (r : ℕ)
    (a b : pairBallVertices G i j r)
    (ha : G.edist i a.val ≤ (r : ℕ∞))
    (p : (pairBallGraph G i j r).Walk a b) :
    ∃ q : (pairBallGraph G i j r).Walk a b, q.length ≤ 4 * r + 1 := by
  by_cases hb : G.edist i b.val ≤ (r : ℕ∞)
  · obtain ⟨q, hq⟩ := pairBall_left_walk_bound G i j r a b ha hb
    exact ⟨q, by omega⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := walk_crosses_cut (pairBallGraph G i j r) p
      {v | G.edist i v.val ≤ (r : ℕ∞)} ha hb
    have hyr : G.edist j y.val ≤ (r : ℕ∞) := y.property.resolve_left hy
    have hbr : G.edist j b.val ≤ (r : ℕ∞) := b.property.resolve_left hb
    obtain ⟨left, hleft⟩ := pairBall_left_walk_bound G i j r a x ha hx
    obtain ⟨right, hright⟩ := pairBall_right_walk_bound G i j r y b hyr hbr
    refine ⟨left.append (right.cons hxy), ?_⟩
    simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons]
    omega

/-- Every actual pair-ball model has natural-valued intrinsic distance at
most `4*r+1`; connectedness is not a hypothesis of this geometric bound. -/
theorem pairBall_distance_bound (i j : V) (r : ℕ)
    (a b : pairBallVertices G i j r) : (pairBallGraph G i j r).dist a b ≤ 4 * r + 1 := by
  by_cases hab : (pairBallGraph G i j r).Reachable a b
  · obtain ⟨p⟩ := hab
    by_cases ha : G.edist i a.val ≤ (r : ℕ∞)
    · obtain ⟨q, hq⟩ := pairBall_walk_bound_of_left G i j r a b ha p
      exact (SimpleGraph.dist_le q).trans hq
    · by_cases hb : G.edist j b.val ≤ (r : ℕ∞)
      · obtain ⟨q, hq⟩ := pairBall_right_walk_bound G i j r a b (a.property.resolve_left ha) hb
        exact (SimpleGraph.dist_le q).trans (by omega)
      · have hbl : G.edist i b.val ≤ (r : ℕ∞) := b.property.resolve_right hb
        obtain ⟨q, hq⟩ := pairBall_walk_bound_of_left G i j r b a hbl p.reverse
        exact (SimpleGraph.dist_le q.reverse).trans (by simpa only [SimpleGraph.Walk.length_reverse] using hq)
  · rw [SimpleGraph.dist_eq_zero_of_not_reachable hab]
    exact Nat.zero_le _

/-- Every isolated component of the pair-ball model inherits this cap in
its own intrinsic metric, rather than only in the ambient metric. -/
theorem pairBall_isolated_distance_bound (i j : V) (r : ℕ)
    (S : Set (pairBallVertices G i j r))
    (hcut : ∀ a ∈ S, ∀ b ∉ S, ¬(pairBallGraph G i j r).Adj a b)
    (a b : S) : ((pairBallGraph G i j r).induce S).dist a b ≤ 4 * r + 1 := by
  rw [isolated_induce_distance (pairBallGraph G i j r) S hcut a b]
  exact pairBall_distance_bound G i j r a.val b.val

end LocalLaw
