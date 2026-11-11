import Mathlib

/-! # A simple finite walk has an old suffix after its last changed edge -/

namespace LocalLaw

variable {V : Type*}

theorem simple_walk_old_suffix (G H : SimpleGraph V) {x y : V}
    (p : H.Walk x y) (hp : p.IsPath) :
    (∃ q : G.Walk x y, q.length = p.length) ∨
      ∃ u v : V, ∃ pre : H.Walk x u, ∃ hnew : H.Adj u v,
        ¬ G.Adj u v ∧ (pre.concat hnew).IsPath ∧
        ∃ suffix : G.Walk v y, pre.length + 1 + suffix.length = p.length := by
  classical
  induction p using SimpleGraph.Walk.concatRec with
  | Hnil => exact Or.inl ⟨SimpleGraph.Walk.nil, rfl⟩
  | @Hconcat x u y p huy ih =>
    have hpP : p.IsPath := by
      rw [SimpleGraph.Walk.concat_eq_append] at hp
      exact hp.of_append_left
    by_cases hold : G.Adj u y
    · rcases ih hpP with ⟨q, hq⟩ | ⟨a, b, pre, hab, hnot, hpre, suffix, hlen⟩
      · exact Or.inl ⟨q.concat hold, by simp only [SimpleGraph.Walk.length_concat, hq]⟩
      · refine Or.inr ⟨a, b, pre, hab, hnot, hpre, suffix.concat hold, ?_⟩
        simp only [SimpleGraph.Walk.length_concat]
        omega
    · exact Or.inr ⟨u, y, p, huy, hold, hp, SimpleGraph.Walk.nil, by simp⟩

theorem simple_walk_common_suffix (G H : SimpleGraph V) {x y : V}
    (p : H.Walk x y) (hp : p.IsPath) :
    (∃ q : (G ⊓ H).Walk x y, q.length = p.length) ∨
      ∃ u v : V, ∃ pre : H.Walk x u, ∃ hnew : H.Adj u v,
        ¬ G.Adj u v ∧ (pre.concat hnew).IsPath ∧
        ∃ suffix : (G ⊓ H).Walk v y, pre.length + 1 + suffix.length = p.length := by
  rcases simple_walk_old_suffix (G ⊓ H) H p hp with h | ⟨u, v, pre, hnew, hnot, hp, q, hlen⟩
  · exact Or.inl h
  · exact Or.inr ⟨u, v, pre, hnew, fun h => hnot ⟨h, hnew⟩, hp, q, hlen⟩

end LocalLaw
