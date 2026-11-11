import LocalLaw.GraphMetricLocality
import LocalLaw.OutsideEdgeCounting

/-!
# Deterministic cardinality bounds for finite graph balls

The deliberately coarse bound |B_r(S)| <= |S|*(d+1)^r follows from one-step
neighborhood expansion under degree<=d. This is sufficient for the paper's
polylogarithmic resampling radius; realizing its N-dependent numerical bound
is a separate asymptotic arithmetic step.
-/

open scoped BigOperators
noncomputable section

namespace LocalLaw

local instance ballCountingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A zero-radius union of balls is exactly its root set. -/
theorem graphSetBall_zero {V : Type*} (G : SimpleGraph V) (S : Set V) :
    graphSetBall G S 0 = S := by
  ext v
  constructor
  · rintro ⟨s, hs, hd⟩
    have heq : G.edist s v = 0 := le_antisymm hd bot_le
    have hsv : s = v := SimpleGraph.edist_eq_zero_iff.mp heq
    exact hsv ▸ hs
  · intro hv
    exact ⟨v, hv, by simp⟩

/-- A successor ball is contained in the preceding ball together with the
neighbors of that ball. The proof splits a reversed short walk at its first edge. -/
theorem graphSetBall_succ_subset {V : Type*} (G : SimpleGraph V) (S : Set V) (r : ℕ) :
    graphSetBall G S (r + 1) ⊆
      graphSetBall G S r ∪ {v | ∃ u ∈ graphSetBall G S r, G.Adj u v} := by
  intro v hv
  obtain ⟨s, hs, p, hp⟩ := (mem_graphSetBall_iff_walk G S (r + 1) v).mp hv
  have hreverse : p.reverse.length ≤ r + 1 := by simpa only [SimpleGraph.Walk.length_reverse] using hp
  generalize hqeq : p.reverse = q at hreverse
  cases q with
  | nil => exact Or.inl ⟨v, hs, by simp⟩
  | @cons v u s hadj q =>
      have hq : q.length ≤ r := by
        simp only [SimpleGraph.Walk.length_cons] at hreverse
        omega
      have hu : u ∈ graphSetBall G S r := by
        apply (mem_graphSetBall_iff_walk G S r u).mpr
        exact ⟨s, hs, q.reverse, by simpa only [SimpleGraph.Walk.length_reverse] using hq⟩
      exact Or.inr ⟨u, hu, hadj.symm⟩

/-- Compatibility between singleton union-balls and the source model's balls. -/
theorem graphSetBall_singleton {V : Type*} (G : SimpleGraph V) (o : V) (r : ℕ) :
    graphSetBall G {o} r = graphBallVertices G o r := by
  ext v
  simp [graphSetBall, graphBallVertices]

section FiniteBalls

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual finite vertex set of a union of graph balls. -/
def graphSetBallFinset (G : SimpleGraph V) (S : Set V) (r : ℕ) : Finset V :=
  (graphSetBall G S r).toFinset

/-- One graph-neighborhood expansion costs at most a factor d+1. -/
theorem closed_neighbor_card_bound (G : SimpleGraph V) (d : ℕ)
    (hdegree : ∀ v, G.degree v ≤ d) (F : Finset V) :
    (F ∪ F.biUnion (fun v => G.neighborFinset v)).card ≤ F.card * (d + 1) := by
  have hsum : (∑ v ∈ F, G.degree v) ≤ F.card * d := by
    calc
      (∑ v ∈ F, G.degree v) ≤ ∑ _v ∈ F, d := Finset.sum_le_sum (fun v _ => hdegree v)
      _ = F.card * d := by simp
  calc
    (F ∪ F.biUnion (fun v => G.neighborFinset v)).card ≤
        F.card + (F.biUnion (fun v => G.neighborFinset v)).card := Finset.card_union_le _ _
    _ ≤ F.card + ∑ v ∈ F, (G.neighborFinset v).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _
    _ = F.card + ∑ v ∈ F, G.degree v := by simp only [SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ F.card + F.card * d := Nat.add_le_add_left hsum _
    _ = F.card * (d + 1) := by ring

/-- Every successor ball vertex belongs to the explicit finite expansion. -/
theorem graphSetBallFinset_succ_subset (G : SimpleGraph V) (S : Set V) (r : ℕ) :
    graphSetBallFinset G S (r + 1) ⊆ graphSetBallFinset G S r ∪
      (graphSetBallFinset G S r).biUnion (fun v => G.neighborFinset v) := by
  intro v hv
  have hv' : v ∈ graphSetBall G S (r + 1) := by simpa only [graphSetBallFinset, Set.mem_toFinset] using hv
  rcases graphSetBall_succ_subset G S r hv' with hsmall | ⟨u, hu, hadj⟩
  · exact Finset.mem_union.mpr (Or.inl (by simpa only [graphSetBallFinset, Set.mem_toFinset] using hsmall))
  · apply Finset.mem_union.mpr
    right
    apply Finset.mem_biUnion.mpr
    exact ⟨u, by simpa only [graphSetBallFinset, Set.mem_toFinset] using hu,
      by simpa only [SimpleGraph.mem_neighborFinset] using hadj⟩

/-- Coarse finite ball growth, proved by successor expansion. -/
theorem graphSetBallFinset_card_bound (G : SimpleGraph V) (S : Set V) (d : ℕ)
    (hdegree : ∀ v, G.degree v ≤ d) (r : ℕ) :
    (graphSetBallFinset G S r).card ≤ S.toFinset.card * (d + 1) ^ r := by
  induction r with
  | zero => simp [graphSetBallFinset, graphSetBall_zero]
  | succ r ih =>
      calc
        (graphSetBallFinset G S (r + 1)).card ≤
            (graphSetBallFinset G S r ∪
              (graphSetBallFinset G S r).biUnion (fun v => G.neighborFinset v)).card :=
          Finset.card_le_card (graphSetBallFinset_succ_subset G S r)
        _ ≤ (graphSetBallFinset G S r).card * (d + 1) :=
          closed_neighbor_card_bound G d hdegree _
        _ ≤ (S.toFinset.card * (d + 1) ^ r) * (d + 1) :=
          Nat.mul_le_mul_right _ ih
        _ = S.toFinset.card * (d + 1) ^ (r + 1) := by rw [pow_succ]; ring

/-- Set-cardinality formulation independent of chosen finite enumerations. -/
theorem graphSetBall_card_bound (G : SimpleGraph V) (S : Set V) (d : ℕ)
    (hdegree : ∀ v, G.degree v ≤ d) (r : ℕ) :
    Nat.card (graphSetBall G S r) ≤ Nat.card S * (d + 1) ^ r := by
  have h := graphSetBallFinset_card_bound G S d hdegree r
  simpa only [graphSetBallFinset, Set.toFinset_card, ← Nat.card_eq_fintype_card] using h

/-- A single radius-r ball contains at most (d+1)^r vertices. -/
theorem graphBall_card_bound (G : SimpleGraph V) (o : V) (d : ℕ)
    (hdegree : ∀ v, G.degree v ≤ d) (r : ℕ) :
    Nat.card (graphBallVertices G o r) ≤ (d + 1) ^ r := by
  have h := graphSetBallFinset_card_bound G {o} d hdegree r
  simpa only [graphSetBallFinset, graphSetBall_singleton, Set.toFinset_card,
    ← Nat.card_eq_fintype_card, Set.toFinset_singleton, Finset.card_singleton, one_mul] using h

end FiniteBalls

namespace RegularGraph

variable {N d : ℕ}

/-- The actual resampling ball has the deterministic polynomial-in-degree
cardinality bound; no tree assumption is needed. -/
theorem ball_card_bound (g : RegularGraph N d) (o : Fin N) (r : ℕ) :
    Nat.card (graphBallVertices g.graph o r) ≤ (d + 1) ^ r :=
  graphBall_card_bound g.graph o d (fun v => (g.regular v).le) r

/-- A numerical radius budget proves the small-set condition required for
outside-edge sampling. -/
theorem ball_small (g : RegularGraph N d) (o : Fin N) (ℓ : ℕ)
    (hbudget : 4 * (d + 1) ^ ℓ ≤ N) :
    4 * Nat.card (graphBallVertices g.graph o ℓ) ≤ N :=
  (Nat.mul_le_mul_left 4 (g.ball_card_bound o ℓ)).trans hbudget

/-- Nonemptiness of the actual radius-ball resampling fiber follows from
regularity and its explicit radius budget. -/
theorem ball_sampling_fiber_nonempty (g : RegularGraph N d) (o : Fin N) (ℓ : ℕ)
    (hN : 0 < N) (hd : 0 < d) (hbudget : 4 * (d + 1) ^ ℓ ≤ N) :
    Nonempty (LocalSamplingFiber g.graph (graphBallVertices g.graph o ℓ)) :=
  g.local_sampling_fiber_nonempty_of_small_set _ hN hd (g.ball_small o ℓ hbudget)

/-- Proposition-5.9 endpoint estimates for the actual radius-ball local
resampling, with its deterministic sample-size estimate fully discharged. -/
theorem ball_endpoint_probability (g : RegularGraph N d) (o : Fin N) (ℓ : ℕ)
    (hN : 0 < N) (hd : 0 < d) (hbudget : 4 * (d + 1) ^ ℓ ≤ N) (v : Fin N) :
    eventMass (finiteUniformWeight (OutsideOrientedEdge g.graph (graphBallVertices g.graph o ℓ)))
      (fun e => outsideEdgeFirst g.graph (graphBallVertices g.graph o ℓ) e = v) ≤ 2 / (N : ℝ) ∧
    eventMass (finiteUniformWeight (OutsideOrientedEdge g.graph (graphBallVertices g.graph o ℓ)))
      (fun e => outsideEdgeSecond g.graph (graphBallVertices g.graph o ℓ) e = v) ≤ 2 / (N : ℝ) :=
  g.outside_endpoint_probability_of_small_set _ hN hd (g.ball_small o ℓ hbudget) v

end RegularGraph

end LocalLaw
