import LocalLaw.GraphModel

/-! # Literal finite-cycle arc walks and image locality -/

namespace LocalLaw

/-- An actual forward arc of any prescribed natural length on the cycle. -/
theorem cycle_forward_walk (n : ℕ) (a : Fin (n + 3)) (k : ℕ) :
    ∃ p : (SimpleGraph.cycleGraph (n + 3)).Walk a (a + (k : Fin (n + 3))), p.length = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨p, hp⟩ := ih
    have hadj : (SimpleGraph.cycleGraph (n + 3)).Adj
        (a + (k : Fin (n + 3))) (a + ((k + 1 : ℕ) : Fin (n + 3))) := by
      apply (SimpleGraph.cycleGraph_adj (n := n + 1)).mpr
      right
      push_cast
      abel
    exact ⟨p.concat hadj, by simp only [SimpleGraph.Walk.length_concat, hp]⟩

/-- The two literal cycle arcs joining any pair have complementary lengths. -/
theorem cycle_two_arc_walks (n : ℕ) (i j : Fin (n + 3)) :
    (∃ p : (SimpleGraph.cycleGraph (n + 3)).Walk i j, p.length = (j - i).val) ∧
    (∃ p : (SimpleGraph.cycleGraph (n + 3)).Walk i j, p.length = n + 3 - (j - i).val) := by
  constructor
  · have hend : i + ((j - i).val : Fin (n + 3)) = j := by rw [Fin.cast_val_eq_self]; abel
    obtain ⟨p, hp⟩ := cycle_forward_walk n i (j - i).val
    exact ⟨p.copy rfl hend, by simpa only [SimpleGraph.Walk.length_copy] using hp⟩
  · have hend : j + ((n + 3 - (j - i).val : ℕ) : Fin (n + 3)) = i := by
      rw [Nat.cast_sub (Nat.le_of_lt (j - i).is_lt), Fin.natCast_self, zero_sub, Fin.cast_val_eq_self]
      abel
    obtain ⟨p, hp⟩ := cycle_forward_walk n j (n + 3 - (j - i).val)
    exact ⟨(p.copy rfl hend).reverse, by simpa only [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_copy] using hp⟩

/-- Actual intrinsic cycle distance is at most either arc length. -/
theorem cycle_distance_le_arcs (n : ℕ) (i j : Fin (n + 3)) :
    (SimpleGraph.cycleGraph (n + 3)).dist i j ≤ (j - i).val ∧
      (SimpleGraph.cycleGraph (n + 3)).dist i j ≤ n + 3 - (j - i).val := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := cycle_two_arc_walks n i j
  exact ⟨hp ▸ SimpleGraph.dist_le p, hq ▸ SimpleGraph.dist_le q⟩

/-- A cycle homomorphism carries all of its vertices into the radius-half
ball of every one of them. Injectivity is unnecessary. -/
theorem cycle_hom_edist_le_half {V : Type*} {G : SimpleGraph V}
    (ell : ℕ) (hell : 3 ≤ ell) (f : SimpleGraph.cycleGraph ell →g G) (i j : Fin ell) :
    G.edist (f i) (f j) ≤ ((ell / 2 : ℕ) : ℕ∞) := by
  obtain ⟨n, rfl⟩ : ∃ n, ell = n + 3 := ⟨ell - 3, by omega⟩
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := cycle_two_arc_walks n i j
  have hhalf : (j - i).val ≤ (n + 3) / 2 ∨ n + 3 - (j - i).val ≤ (n + 3) / 2 := by omega
  rcases hhalf with h | h
  · exact (SimpleGraph.edist_le (p.map f)).trans (by simpa only [SimpleGraph.Walk.length_map, hp] using ENat.coe_le_coe.mpr h)
  · exact (SimpleGraph.edist_le (q.map f)).trans (by simpa only [SimpleGraph.Walk.length_map, hq] using ENat.coe_le_coe.mpr h)

/-- Every image vertex of a cycle of length at most 2R+1 lies in the actual
radius-R ball around any image vertex. -/
theorem cycle_hom_image_ball {V : Type*} {G : SimpleGraph V} (ell R : ℕ)
    (hell : 3 ≤ ell) (hsize : ell ≤ 2 * R + 1) (f : SimpleGraph.cycleGraph ell →g G)
    (i j : Fin ell) : f j ∈ graphBallVertices G (f i) R := by
  exact (cycle_hom_edist_le_half ell hell f i j).trans (ENat.coe_le_coe.mpr (by omega))

end LocalLaw
