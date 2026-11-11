import LocalLaw.BoundaryDepthAndIncidence
import LocalLaw.PairRestrictionIdentity

/-! # Exact boundary depth for the union of two target balls

Every crossing edge of the switched pair restriction starts at distance at
least r from both targets. Newly created crossing-edge boundary charges are
therefore supported on the actual outer layer.
-/

noncomputable section
namespace LocalLaw
variable {V : Type*}

theorem pair_boundary_inner_edist_lower (G : SimpleGraph V) (i j : V) (r : ℕ)
    (a : BoundaryOrientedEdge G (pairBallVertices G i j r)) :
    (r:ℕ∞)≤G.edist i a.val.1 ∧ (r:ℕ∞)≤G.edist j a.val.1 := by
  have hone (x : V) (hnot : a.val.2∉graphBallVertices G x r) :
      (r:ℕ∞)≤G.edist x a.val.1 := by
    by_cases hx : a.val.1∈graphBallVertices G x r
    · exact (ball_boundary_inner_edist G x r ⟨a.val,a.property.1,hx,hnot⟩).ge
    · exact (le_of_lt (lt_of_not_ge hx))
  exact ⟨hone i (fun h => a.property.2.2 (Or.inl h)),
    hone j (fun h => a.property.2.2 (Or.inr h))⟩

theorem pair_boundary_inner_edist_min (G : SimpleGraph V) (i j : V) (r : ℕ)
    (a : BoundaryOrientedEdge G (pairBallVertices G i j r)) :
    min (G.edist i a.val.1) (G.edist j a.val.1)=(r:ℕ∞) := by
  have hlo := pair_boundary_inner_edist_lower G i j r a
  apply le_antisymm
  · rcases a.property.2.1 with hi|hj
    · exact (min_le_left _ _).trans hi
    · exact (min_le_right _ _).trans hj
  · exact le_min hlo.1 hlo.2

theorem pair_near_vertex_no_crossing_edge (G : SimpleGraph V) (i j : V) (r : ℕ)
    (v w : V) (hnear : G.edist i v<(r:ℕ∞) ∨ G.edist j v<(r:ℕ∞))
    (hw : w∉pairBallVertices G i j r) : ¬G.Adj v w := by
  intro hvw
  have hv : v∈pairBallVertices G i j r := hnear.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le)
  let a : BoundaryOrientedEdge G (pairBallVertices G i j r) := ⟨(v,w),hvw,hv,hw⟩
  have hh := pair_boundary_inner_edist_lower G i j r a
  rcases hnear with hi|hj
  · exact not_lt_of_ge hh.1 hi
  · exact not_lt_of_ge hh.2 hj

end LocalLaw
