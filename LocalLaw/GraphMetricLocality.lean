import Mathlib

/-!
# Locality of graph neighborhoods

Changing edges entirely inside the root set leaves its union of radius balls
unchanged. The proof transfers a walk, discarding a prefix when an internal
root edge is encountered. A second locality result treats changes outside all
edges incident to the original ball. Distances are extended graph distances,
so disconnected vertices and empty root sets need no special conventions.
-/

namespace LocalLaw
variable {V : Type*}

/-- The union of closed radius-r balls centered at a root set. -/
def graphSetBall (G : SimpleGraph V) (S : Set V) (radius : ℕ) : Set V :=
  {v | ∃ s ∈ S, G.edist s v ≤ (radius : ℕ∞)}

/-- Finite-radius membership is exactly existence of a suitably short walk. -/
theorem mem_graphSetBall_iff_walk (G : SimpleGraph V) (S : Set V) (radius : ℕ) (v : V) :
    v ∈ graphSetBall G S radius ↔
      ∃ s ∈ S, ∃ p : G.Walk s v, p.length ≤ radius := by
  constructor
  · rintro ⟨s, hs, hdist⟩
    have hfinite : G.edist s v ≠ ⊤ := ne_of_lt (hdist.trans_lt (ENat.coe_lt_top radius))
    obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfinite
    exact ⟨s, hs, p, ENat.coe_le_coe.mp (hp.trans_le hdist)⟩
  · rintro ⟨s, hs, p, hp⟩
    exact ⟨s, hs, (SimpleGraph.edist_le p).trans (ENat.coe_le_coe.mpr hp)⟩

/-- Under changes inside S×S, a walk can be transferred directly or restarted
at a root after discarding a prefix. The resulting length never increases. -/
theorem walk_transfer_or_restart (G H : SimpleGraph V) (S : Set V)
    (hagree : ∀ x y, x ∉ S ∨ y ∉ S → (G.Adj x y ↔ H.Adj x y))
    {x y : V} (p : G.Walk x y) :
    (∃ q : H.Walk x y, q.length ≤ p.length) ∨
      ∃ s ∈ S, ∃ q : H.Walk s y, q.length ≤ p.length := by
  classical
  induction p with
  | nil => exact Or.inl ⟨SimpleGraph.Walk.nil, le_rfl⟩
  | @cons x u y hxu p ih =>
      rcases ih with ⟨q, hq⟩ | ⟨s, hs, q, hq⟩
      · by_cases hroot : x ∈ S ∧ u ∈ S
        · exact Or.inr ⟨u, hroot.2, q, by simpa only [SimpleGraph.Walk.length_cons] using hq.trans (Nat.le_succ _)⟩
        · have hh : H.Adj x u := (hagree x u (not_and_or.mp hroot)).mp hxu
          exact Or.inl ⟨q.cons hh, by simpa only [SimpleGraph.Walk.length_cons] using Nat.succ_le_succ hq⟩
      · exact Or.inr ⟨s, hs, q, by simpa only [SimpleGraph.Walk.length_cons] using hq.trans (Nat.le_succ _)⟩

/-- Any root-to-vertex walk survives internal-root-set rewiring, possibly
starting at a different root and with a shorter length. -/
theorem root_walk_transfer (G H : SimpleGraph V) (S : Set V)
    (hagree : ∀ x y, x ∉ S ∨ y ∉ S → (G.Adj x y ↔ H.Adj x y))
    {s v : V} (hs : s ∈ S) (p : G.Walk s v) :
    ∃ t ∈ S, ∃ q : H.Walk t v, q.length ≤ p.length := by
  rcases walk_transfer_or_restart G H S hagree p with ⟨q, hq⟩ | hroot
  · exact ⟨s, hs, q, hq⟩
  · exact hroot

/-- The union of root balls is invariant under arbitrary changes of edges
whose two endpoints both belong to the root set. -/
theorem graphSetBall_eq_of_internal_changes (G H : SimpleGraph V) (S : Set V)
    (hagree : ∀ x y, x ∉ S ∨ y ∉ S → (G.Adj x y ↔ H.Adj x y)) (radius : ℕ) :
    graphSetBall G S radius = graphSetBall H S radius := by
  ext v
  rw [mem_graphSetBall_iff_walk, mem_graphSetBall_iff_walk]
  constructor
  · rintro ⟨s, hs, p, hp⟩
    obtain ⟨t, ht, q, hq⟩ := root_walk_transfer G H S hagree hs p
    exact ⟨t, ht, q, hq.trans hp⟩
  · rintro ⟨s, hs, p, hp⟩
    obtain ⟨t, ht, q, hq⟩ := root_walk_transfer H G S
      (fun x y h => (hagree x y h).symm) hs p
    exact ⟨t, ht, q, hq.trans hp⟩

/-- Reverse a walk from a root while using its already-transferred suffix to
certify membership in the original ball. This is a first-exit argument without
choosing a shortest path. -/
theorem walk_transfer_of_incident_ball_agreement (G H : SimpleGraph V) (S : Set V)
    (radius : ℕ)
    (hagree : ∀ x y, x ∈ graphSetBall G S radius ∨ y ∈ graphSetBall G S radius →
      (G.Adj x y ↔ H.Adj x y))
    {s v : V} (hs : s ∈ S) (p : H.Walk v s) (hp : p.length ≤ radius) :
    ∃ q : G.Walk v s, q.length = p.length := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons v u s hvu p ih =>
      have hplen : p.length ≤ radius := by
        simp only [SimpleGraph.Walk.length_cons] at hp
        omega
      obtain ⟨q, hq⟩ := ih hs hplen
      have hu : u ∈ graphSetBall G S radius := by
        apply (mem_graphSetBall_iff_walk G S radius u).mpr
        exact ⟨s, hs, q.reverse, by simpa only [SimpleGraph.Walk.length_reverse, hq] using hplen⟩
      have hGvu : G.Adj v u := (hagree v u (Or.inr hu)).mpr hvu
      exact ⟨q.cons hGvu, by simp only [SimpleGraph.Walk.length_cons, hq]⟩

/-- No new vertex can enter the original ball if all incident edges agree. -/
theorem graphSetBall_subset_of_incident_agreement (G H : SimpleGraph V) (S : Set V)
    (radius : ℕ)
    (hagree : ∀ x y, x ∈ graphSetBall G S radius ∨ y ∈ graphSetBall G S radius →
      (G.Adj x y ↔ H.Adj x y)) :
    graphSetBall H S radius ⊆ graphSetBall G S radius := by
  intro v hv
  obtain ⟨s, hs, p, hp⟩ := (mem_graphSetBall_iff_walk H S radius v).mp hv
  obtain ⟨q, hq⟩ := walk_transfer_of_incident_ball_agreement G H S radius hagree hs
    p.reverse (by simpa only [SimpleGraph.Walk.length_reverse] using hp)
  apply (mem_graphSetBall_iff_walk G S radius v).mpr
  exact ⟨s, hs, q.reverse, by simpa only [SimpleGraph.Walk.length_reverse, hq] using hp⟩

/-- If the two graphs agree on all edges incident to the original union of
balls, their radius neighborhoods agree exactly. -/
theorem graphSetBall_eq_of_incident_agreement (G H : SimpleGraph V) (S : Set V)
    (radius : ℕ)
    (hagree : ∀ x y, x ∈ graphSetBall G S radius ∨ y ∈ graphSetBall G S radius →
      (G.Adj x y ↔ H.Adj x y)) :
    graphSetBall G S radius = graphSetBall H S radius := by
  have hHG := graphSetBall_subset_of_incident_agreement G H S radius hagree
  have hGH : graphSetBall G S radius ⊆ graphSetBall H S radius := by
    apply graphSetBall_subset_of_incident_agreement H G S radius
    intro x y hxy
    apply (hagree x y ?_).symm
    rcases hxy with hx | hy
    · exact Or.inl (hHG hx)
    · exact Or.inr (hHG hy)
  exact Set.Subset.antisymm hGH hHG

/-- The induced graph on the original ball is unchanged under incident-edge
agreement. No isomorphism or relabeling is needed on this common vertex set. -/
theorem induce_graphSetBall_eq_of_incident_agreement (G H : SimpleGraph V) (S : Set V)
    (radius : ℕ)
    (hagree : ∀ x y, x ∈ graphSetBall G S radius ∨ y ∈ graphSetBall G S radius →
      (G.Adj x y ↔ H.Adj x y)) :
    G.induce (graphSetBall G S radius) = H.induce (graphSetBall G S radius) := by
  ext x y
  exact hagree x.val y.val (Or.inl x.property)

/-- Use H's edges entirely inside S and G's edges everywhere else. This
intermediate graph separates own-root rewiring from distant modifications. -/
def internalRootPatch (G H : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj x y := (x ∈ S ∧ y ∈ S ∧ H.Adj x y) ∨ ((x ∉ S ∨ y ∉ S) ∧ G.Adj x y)
  symm := by
    intro x y hxy
    rcases hxy with ⟨hx, hy, hH⟩ | ⟨hS, hG⟩
    · exact Or.inl ⟨hy, hx, hH.symm⟩
    · exact Or.inr ⟨hS.symm, hG.symm⟩
  loopless := by
    intro x hxx
    rcases hxx with ⟨_, _, hH⟩ | ⟨_, hG⟩
    · exact H.loopless x hH
    · exact G.loopless x hG

/-- Patching only root-internal edges preserves every root neighborhood. -/
theorem graphSetBall_internalRootPatch (G H : SimpleGraph V) (S : Set V) (radius : ℕ) :
    graphSetBall (internalRootPatch G H S) S radius = graphSetBall G S radius := by
  apply graphSetBall_eq_of_internal_changes
  intro x y hS
  change ((x ∈ S ∧ y ∈ S ∧ H.Adj x y) ∨ ((x ∉ S ∨ y ∉ S) ∧ G.Adj x y)) ↔ G.Adj x y
  aesop

/-- Simultaneously changing root-internal edges and edges wholly away from
the original ball preserves the ball. This combines own-triple rewiring with
the distant switchings in a local resampling family. -/
theorem graphSetBall_eq_of_internal_or_distant_changes (G H : SimpleGraph V) (S : Set V)
    (radius : ℕ)
    (hagree : ∀ x y, x ∈ graphSetBall G S radius ∨ y ∈ graphSetBall G S radius →
      (x ∉ S ∨ y ∉ S) → (G.Adj x y ↔ H.Adj x y)) :
    graphSetBall G S radius = graphSetBall H S radius := by
  let K := internalRootPatch G H S
  have hKG : graphSetBall K S radius = graphSetBall G S radius :=
    graphSetBall_internalRootPatch G H S radius
  have hKH : graphSetBall K S radius = graphSetBall H S radius := by
    apply graphSetBall_eq_of_incident_agreement
    intro x y hxy
    have hxyG : x ∈ graphSetBall G S radius ∨ y ∈ graphSetBall G S radius := by
      simpa only [hKG] using hxy
    change ((x ∈ S ∧ y ∈ S ∧ H.Adj x y) ∨ ((x ∉ S ∨ y ∉ S) ∧ G.Adj x y)) ↔ H.Adj x y
    by_cases hroot : x ∈ S ∧ y ∈ S
    · aesop
    · have hout := not_and_or.mp hroot
      have hadj := hagree x y hxyG hout
      aesop
  exact hKG.symm.trans hKH

/-- Set-to-set separation written without an infimum or nonempty-set side
condition, exactly as used by the local resampling isolation test. -/
def graphSetsSeparated (G : SimpleGraph V) (S U : Set V) (radius : ℕ) : Prop :=
  ∀ s ∈ S, ∀ u ∈ U, (radius : ℕ∞) < G.edist s u

theorem graphSetsSeparated_iff_disjoint_ball (G : SimpleGraph V) (S U : Set V) (radius : ℕ) :
    graphSetsSeparated G S U radius ↔ Disjoint (graphSetBall G S radius) U := by
  constructor
  · intro h
    apply Set.disjoint_left.mpr
    rintro u ⟨s, hs, hdist⟩ hu
    exact not_lt_of_ge hdist (h s hs u hu)
  · intro h s hs u hu
    by_contra hdist
    have hle : G.edist s u ≤ radius := le_of_not_gt hdist
    exact (Set.disjoint_left.mp h) ⟨s, hs, hle⟩ hu

/-- Internal rewiring at a root set preserves its distance isolation from
any other set. This is the metric ingredient for the paper's J-invariance. -/
theorem graphSetsSeparated_iff_of_internal_changes (G H : SimpleGraph V) (S U : Set V)
    (hagree : ∀ x y, x ∉ S ∨ y ∉ S → (G.Adj x y ↔ H.Adj x y)) (radius : ℕ) :
    graphSetsSeparated G S U radius ↔ graphSetsSeparated H S U radius := by
  rw [graphSetsSeparated_iff_disjoint_ball, graphSetsSeparated_iff_disjoint_ball,
    graphSetBall_eq_of_internal_changes G H S hagree radius]

/-- Isolation is unchanged under the combined own-internal and distant
modifications, once the explicit local adjacency condition is verified. -/
theorem graphSetsSeparated_iff_of_internal_or_distant_changes
    (G H : SimpleGraph V) (S U : Set V) (radius : ℕ)
    (hagree : ∀ x y, x ∈ graphSetBall G S radius ∨ y ∈ graphSetBall G S radius →
      (x ∉ S ∨ y ∉ S) → (G.Adj x y ↔ H.Adj x y)) :
    graphSetsSeparated G S U radius ↔ graphSetsSeparated H S U radius := by
  rw [graphSetsSeparated_iff_disjoint_ball, graphSetsSeparated_iff_disjoint_ball,
    graphSetBall_eq_of_internal_or_distant_changes G H S radius hagree]

end LocalLaw
