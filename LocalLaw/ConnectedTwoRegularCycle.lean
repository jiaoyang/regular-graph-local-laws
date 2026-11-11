import LocalLaw.CycleWalkEmbedding

/-!
# Actual finite connected two-regular graphs are literal cycles

A simple cycle witness is locally onto because each source and target vertex
has exactly two neighbors. Its nonempty image is closed under adjacency, so
connectedness makes it globally onto. No graph isomorphism is assumed.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance twoRegularDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section FiniteGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

omit [DecidableEq V] in
/-- An injective cycle homomorphism into a two-regular graph maps each
neighbor set bijectively onto the actual ambient neighbor set. -/
theorem two_regular_cycle_neighbor_surjective (hdeg : ∀ v, G.degree v = 2)
    (ell : ℕ) (hell : 3 ≤ ell) (f : Fin ell ↪ V)
    (hf : ∀ i j, (SimpleGraph.cycleGraph ell).Adj i j → G.Adj (f i) (f j))
    (i : Fin ell) (w : V) (hiw : G.Adj (f i) w) :
    ∃ j, (SimpleGraph.cycleGraph ell).Adj i j ∧ f j = w := by
  let F : (SimpleGraph.cycleGraph ell).neighborSet i → G.neighborSet (f i) :=
    fun j => ⟨f j.val, hf i j.val j.property⟩
  have hinj : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    apply f.injective
    exact congrArg Subtype.val hab
  have hsource : Fintype.card ((SimpleGraph.cycleGraph ell).neighborSet i) = 2 := by
    have hh := cycleGraph_degree ell hell i
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh
    simpa only [Nat.card_eq_fintype_card] using hh
  have htarget : Fintype.card (G.neighborSet (f i)) = 2 := by
    simpa only [SimpleGraph.card_neighborSet_eq_degree] using hdeg (f i)
  have hbij := (Fintype.bijective_iff_injective_and_card F).mpr ⟨hinj, hsource.trans htarget.symm⟩
  obtain ⟨j, hj⟩ := hbij.2 ⟨w, hiw⟩
  exact ⟨j.val, j.property, congrArg Subtype.val hj⟩

omit [DecidableEq V] in
/-- Such an injective cycle homomorphism already reflects every adjacency. -/
theorem two_regular_cycle_adj_iff (hdeg : ∀ v, G.degree v = 2)
    (ell : ℕ) (hell : 3 ≤ ell) (f : Fin ell ↪ V)
    (hf : ∀ i j, (SimpleGraph.cycleGraph ell).Adj i j → G.Adj (f i) (f j)) (i j : Fin ell) :
    G.Adj (f i) (f j) ↔ (SimpleGraph.cycleGraph ell).Adj i j := by
  constructor
  · intro hij
    obtain ⟨a, ha, heq⟩ := two_regular_cycle_neighbor_surjective G hdeg ell hell f hf i (f j) hij
    exact f.injective heq ▸ ha
  · exact hf i j

omit [DecidableEq V] in
/-- Its image is all vertices of a connected graph, by actual walk induction. -/
theorem two_regular_cycle_surjective (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 2)
    (ell : ℕ) (hell : 3 ≤ ell) (f : Fin ell ↪ V)
    (hf : ∀ i j, (SimpleGraph.cycleGraph ell).Adj i j → G.Adj (f i) (f j)) :
    Function.Surjective f := by
  let i₀ : Fin ell := ⟨0, by omega⟩
  have hwalk : ∀ {a b : V}, G.Walk a b → (∃ i, f i = a) → ∃ j, f j = b := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons a b c hab p ih =>
      rintro ⟨i, rfl⟩
      obtain ⟨j, _, hj⟩ := two_regular_cycle_neighbor_surjective G hdeg ell hell f hf i b hab
      exact ih ⟨j, hj⟩
  intro v
  obtain ⟨p⟩ := hconn.preconnected (f i₀) v
  exact hwalk p ⟨i₀, rfl⟩

omit [DecidableEq V] in
/-- A finite connected graph with every degree two contains an actual simple
cycle: degree-sum and tree cardinality preclude acyclicity. -/
theorem connected_two_regular_exists_cycle (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 2) :
    ∃ o : V, ∃ p : G.Walk o o, p.IsCycle := by
  classical
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp only [hdeg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hnot : ¬G.IsAcyclic := by
    intro hacyclic
    have htree : G.IsTree := ⟨hconn, hacyclic⟩
    have hcard := htree.card_edgeFinset
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.cast_id] at hsum hcard
    omega
  apply Classical.byContradiction
  intro hn
  apply hnot
  intro o p hp
  exact hn ⟨o, p, hp⟩

omit [DecidableEq V] in
/-- Constructive classification from the actual finite graph hypotheses. -/
theorem connected_two_regular_cycle_iso (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 2) :
    ∃ ell : ℕ, 3 ≤ ell ∧ Nonempty (SimpleGraph.cycleGraph ell ≃g G) := by
  obtain ⟨o, p, hp⟩ := connected_two_regular_exists_cycle G hconn hdeg
  let f := cycleWalkInjection p hp
  have hf : ∀ i j, (SimpleGraph.cycleGraph p.length).Adj i j → G.Adj (f i) (f j) :=
    cycleWalkInjection_adj p hp
  have hsurj := two_regular_cycle_surjective G hconn hdeg p.length hp.three_le_length f hf
  let e : Fin p.length ≃ V := Equiv.ofBijective f ⟨f.injective, hsurj⟩
  refine ⟨p.length, hp.three_le_length, ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩⟩
  intro i j
  exact two_regular_cycle_adj_iff G hdeg p.length hp.three_le_length f hf i j

omit [DecidableEq V] in
/-- The literal cycle length equals the actual finite vertex count. -/
theorem connected_two_regular_cycle_card_iso (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 2) :
    3 ≤ Fintype.card V ∧ Nonempty (SimpleGraph.cycleGraph (Fintype.card V) ≃g G) := by
  obtain ⟨ell, hell, ⟨e⟩⟩ := connected_two_regular_cycle_iso G hconn hdeg
  have hcard : ell = Fintype.card V := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e.toEquiv
  subst ell
  exact ⟨hell, ⟨e⟩⟩

end FiniteGraph
end
end LocalLaw
