import LocalLaw.GraphBallCounting

/-!
# Moving one radius unit into the center set

Expanding the center set by one step and reducing the remaining radius by
one preserves the literal union of balls. The proof splits an actual walk
at its first edge, so it also covers disconnected and empty center sets.
-/

namespace LocalLaw
variable {V : Type*}

theorem graphSetBall_expand_centers_one (G : SimpleGraph V) (S : Set V) (r : ℕ) :
    graphSetBall G (graphSetBall G S 1) r = graphSetBall G S (r + 1) := by
  ext v
  constructor
  · rintro ⟨u, ⟨s, hs, hsu⟩, huv⟩
    refine ⟨s, hs, ?_⟩
    calc
      G.edist s v ≤ G.edist s u + G.edist u v := G.edist_triangle
      _ ≤ (1 : ℕ∞) + (r : ℕ∞) := add_le_add hsu huv
      _ = ((r + 1 : ℕ) : ℕ∞) := by norm_cast; omega
  · intro hv
    obtain ⟨s, hs, p, hp⟩ := (mem_graphSetBall_iff_walk G S (r + 1) v).mp hv
    cases p with
    | nil =>
      exact ⟨v, ⟨v, hs, by simp⟩, by simp⟩
    | @cons s u v hsu p =>
      have hu : u ∈ graphSetBall G S 1 :=
        ⟨s, hs, le_of_eq (SimpleGraph.edist_eq_one_iff_adj.mpr hsu)⟩
      have hlen : p.length ≤ r := by
        simp only [SimpleGraph.Walk.length_cons] at hp
        omega
      exact (mem_graphSetBall_iff_walk G (graphSetBall G S 1) r v).mpr ⟨u, hu, p, hlen⟩

end LocalLaw
