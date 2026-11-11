import LocalLaw.CycleCounting

/-!
# A concrete simple cycle walk gives a labelled cycle pattern

Vertices are read from the actual walk, before the repeated last endpoint.
Cycle simplicity proves injectivity. Consecutive edges, including the closing
edge, prove that the mapped cycle-graph pattern is a subgraph of the ambient
graph. This connects graph-geometric witnesses to the finite counting API.
-/

noncomputable section
namespace LocalLaw

local instance cycleWalkDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section General
variable {V : Type*} {G : SimpleGraph V} {o : V}

/-- The last repeated endpoint is omitted from a cycle's vertex labels. -/
def cycleWalkInjection (p : G.Walk o o) (hp : p.IsCycle) : Fin p.length ↪ V where
  toFun i := p.getVert i.val
  inj' := by
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn' (by change i.val ≤ p.length - 1; omega)
      (by change j.val ≤ p.length - 1; omega) hij

/-- Closed-walk adjacency also holds at the modular closing step. -/
theorem closedWalk_next_adj (p : G.Walk o o) (n : ℕ) (hlen : p.length = n + 1)
    (i : Fin (n + 1)) : G.Adj (p.getVert i.val) (p.getVert (i + 1).val) := by
  rw [Fin.val_add_one]
  split_ifs with hi
  · subst i
    simp only [Fin.val_last]
    have hadj := p.adj_getVert_succ (i := n) (by omega)
    have heq : p.getVert (n + 1) = p.getVert 0 := by
      rw [← hlen, p.getVert_length, p.getVert_zero]
    rw [heq] at hadj
    exact hadj
  · exact p.adj_getVert_succ (by omega)

/-- Every cycle-graph adjacency is an edge of the actual closed walk. -/
theorem closedWalk_cycleGraph_adj (p : G.Walk o o) (n : ℕ) (hlen : p.length = n)
    (hn : 2 ≤ n) (i j : Fin n) (hij : (SimpleGraph.cycleGraph n).Adj i j) :
    G.Adj (p.getVert i.val) (p.getVert j.val) := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    cases n with
    | zero => omega
    | succ n =>
      rcases SimpleGraph.cycleGraph_adj.mp hij with h | h
      · have heq : i = j + 1 := by
          have hh := sub_eq_iff_eq_add.mp h
          simpa only [add_comm] using hh
        rw [heq]
        exact (closedWalk_next_adj p _ hlen j).symm
      · have heq : j = i + 1 := by
          have hh := sub_eq_iff_eq_add.mp h
          simpa only [add_comm] using hh
        rw [heq]
        exact closedWalk_next_adj p _ hlen i

theorem cycleWalkInjection_adj (p : G.Walk o o) (hp : p.IsCycle) (i j : Fin p.length)
    (hij : (SimpleGraph.cycleGraph p.length).Adj i j) :
    G.Adj (cycleWalkInjection p hp i) (cycleWalkInjection p hp j) :=
  closedWalk_cycleGraph_adj p p.length rfl (by linarith [hp.three_le_length]) i j hij

theorem cycleWalkInjection_mem_support (p : G.Walk o o) (hp : p.IsCycle) (i : Fin p.length) :
    cycleWalkInjection p hp i ∈ p.support := p.getVert_mem_support i.val

theorem cycleWalkInjection_root (p : G.Walk o o) (hp : p.IsCycle) :
    ∃ i : Fin p.length, cycleWalkInjection p hp i = o := by
  refine ⟨⟨0, by linarith [hp.three_le_length]⟩, ?_⟩
  exact p.getVert_zero

end General

section Finite
variable {N : ℕ} {G : SimpleGraph (Fin N)} {o : Fin N}

/-- The actual labelled required-edge pattern associated with a cycle witness. -/
theorem cycleWalkPattern_le (p : G.Walk o o) (hp : p.IsCycle) :
    cyclePattern (cycleWalkInjection p hp) ≤ G := by
  apply (mappedPattern_le_iff _ _ _).mpr
  exact cycleWalkInjection_adj p hp

/-- A geometric cycle witness gives a positive actual labelled-cycle count. -/
theorem labelledCycleCount_pos_of_cycle (p : G.Walk o o) (hp : p.IsCycle) :
    0 < labelledCycleCount p.length G := by
  unfold labelledCycleCount labelledPatternCount
  apply Finset.card_pos.mpr
  exact ⟨cycleWalkInjection p hp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, cycleWalkPattern_le p hp⟩⟩


/-- The same bridge preserves support when the witness lives in an induced
subgraph, as required for an actual graph-ball cycle. -/
theorem induced_cycle_pattern_witness (S : Set (Fin N)) (o : S)
    (p : (G.induce S).Walk o o) (hp : p.IsCycle) :
    ∃ f : Fin p.length ↪ Fin N,
      cyclePattern f ≤ G ∧ (∀ i, f i ∈ S) ∧ ∃ i, f i = o.val := by
  let f : Fin p.length ↪ Fin N := (cycleWalkInjection p hp).trans
    ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · apply (mappedPattern_le_iff _ _ _).mpr
    intro i j hij
    exact cycleWalkInjection_adj p hp i j hij
  · intro i
    exact (cycleWalkInjection p hp i).property
  · obtain ⟨i, hi⟩ := cycleWalkInjection_root p hp
    exact ⟨i, congrArg Subtype.val hi⟩

theorem labelledCycleCount_pos_of_induced_cycle (S : Set (Fin N)) (o : S)
    (p : (G.induce S).Walk o o) (hp : p.IsCycle) :
    0 < labelledCycleCount p.length G := by
  obtain ⟨f, hle, _, _⟩ := induced_cycle_pattern_witness S o p hp
  unfold labelledCycleCount labelledPatternCount
  apply Finset.card_pos.mpr
  exact ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩⟩

end Finite
end LocalLaw
