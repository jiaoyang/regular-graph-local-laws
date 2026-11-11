import LocalLaw.LeafReferenceReduction
import LocalLaw.ConnectedTwoRegularCycle
import LocalLaw.ExcessCutset

/-! # Exact graph geometry for pruning a finite unicyclic graph -/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance unicyclicPruningDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section FiniteGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

omit [DecidableEq V] in
/-- An excess-one connected graph has as many edges as vertices. -/
theorem unicyclic_edge_card (hconn : G.Connected) (hexcess : graphExcess G = 1) :
    graphEdgeCount G = Fintype.card V := by
  have hh := connected_graph_excess_euler G hconn
  rw [hexcess, Nat.card_eq_fintype_card] at hh
  omega

omit [DecidableEq V] in
/-- Its actual sum of degrees is twice the finite vertex count. -/
theorem unicyclic_degree_sum (hconn : G.Connected) (hexcess : graphExcess G = 1) :
    (∑ v, G.degree v) = 2 * Fintype.card V := by
  have hh := G.sum_degrees_eq_twice_card_edges
  have he := unicyclic_edge_card G hconn hexcess
  simp only [graphEdgeCount, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at he
  exact hh.trans (congrArg (fun n => 2 * n) he)

omit [DecidableEq V] in
/-- A connected balanced graph has no isolated vertex. -/
theorem balanced_connected_degree_pos (hconn : G.Connected)
    (hsum : (∑ v, G.degree v) = 2 * Fintype.card V) (v : V) : 0 < G.degree v := by
  apply Nat.pos_of_ne_zero
  intro hv
  have hno : ∀ w, ¬G.Adj v w := by
    intro w hadj
    have hh := (G.degree_pos_iff_exists_adj v).mpr ⟨w, hadj⟩
    omega
  have hall : ∀ w, w = v := by
    intro w
    obtain ⟨p⟩ := hconn.preconnected v w
    cases p with
    | nil => rfl
    | cons hadj p => exact False.elim (hno _ hadj)
  have hzero : ∀ w, G.degree w = 0 := by intro w; rw [hall w]; exact hv
  simp only [hzero, Finset.sum_const_zero] at hsum
  have hnon : Nonempty V := hconn.nonempty
  have hcard : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hnon
  omega

omit [DecidableEq V] in
/-- Degree balance forces either a two-regular core or an actual leaf. -/
theorem balanced_connected_two_regular_or_leaf (hconn : G.Connected)
    (hsum : (∑ v, G.degree v) = 2 * Fintype.card V) :
    (∀ v, G.degree v = 2) ∨ ∃ v, G.degree v = 1 := by
  classical
  by_cases htwo : ∀ v, G.degree v = 2
  · exact Or.inl htwo
  · right
    have hlow : ∃ v, G.degree v < 2 := by
      apply Classical.byContradiction
      intro hn
      have hle : ∀ v, 2 ≤ G.degree v := fun v => Nat.le_of_not_gt (fun hh => hn ⟨v, hh⟩)
      have heq : (∑ _v : V, (2 : ℕ)) = ∑ v, G.degree v := by
        rw [hsum]
        simp [nsmul_eq_mul, mul_comm]
      have hall := (Finset.sum_eq_sum_iff_of_le (fun v (_ : v ∈ Finset.univ) => hle v)).mp heq
      exact htwo (fun v => (hall v (Finset.mem_univ v)).symm)
    obtain ⟨v, hv⟩ := hlow
    have hp := balanced_connected_degree_pos G hconn hsum v
    exact ⟨v, by omega⟩

omit [DecidableEq V] in
/-- A simple path between retained vertices cannot visit a degree-one vertex.
The resulting path is genuinely in the induced deletion and has equal length. -/
theorem leaf_path_delete (v u : V) (hv : G.degree v = 1) (hvu : G.Adj v u)
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) (ha : a ≠ v) (hb : b ≠ v) :
    ∃ q : (G.induce {x | x ≠ v}).Walk ⟨a, ha⟩ ⟨b, hb⟩, q.length = p.length := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons a c b hac p ih =>
    have hc : c ≠ v := by
      intro hcv
      subst c
      cases p with
      | nil => exact hb rfl
      | @cons v w b hvw q =>
        have hau : a = u := (leaf_adj_iff G v u hv hvu a).mp hac.symm
        have hwu : w = u := (leaf_adj_iff G v u hv hvu w).mp hvw
        have hmem : a ∈ (SimpleGraph.Walk.cons hvw q).support := by
          rw [hau, ← hwu]
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
          exact Or.inr q.start_mem_support
        exact ((SimpleGraph.Walk.cons_isPath_iff hac (SimpleGraph.Walk.cons hvw q)).mp hp).2 hmem
    obtain ⟨q, hq⟩ := ih hp.of_cons hc hb
    exact ⟨q.cons (show (G.induce {x | x ≠ v}).Adj ⟨a, ha⟩ ⟨c, hc⟩ from hac),
      by simp only [SimpleGraph.Walk.length_cons, hq]⟩

omit [DecidableEq V] in
/-- Deleting a leaf preserves connectedness of the actual remaining graph. -/
theorem leaf_delete_connected (hconn : G.Connected) (v u : V) (hv : G.degree v = 1)
    (hvu : G.Adj v u) : (G.induce {x | x ≠ v}).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨u, hvu.ne.symm⟩, ?_⟩
  intro b
  obtain ⟨p, hp⟩ := hconn.exists_isPath u b.val
  obtain ⟨q, _⟩ := leaf_path_delete G v u hv hvu p hp hvu.ne.symm b.property
  exact q.reachable

omit [DecidableEq V] in
/-- Retained intrinsic distances are unchanged by genuine leaf deletion. -/
theorem leaf_delete_distance (hconn : G.Connected) (v u : V) (hv : G.degree v = 1)
    (hvu : G.Adj v u) (a b : {x : V // x ≠ v}) :
    (G.induce {x | x ≠ v}).dist a b = G.dist a.val b.val := by
  apply le_antisymm
  · obtain ⟨p, hp, hlen⟩ := (hconn.preconnected a.val b.val).exists_path_of_dist
    obtain ⟨q, hq⟩ := leaf_path_delete G v u hv hvu p hp a.property b.property
    exact (SimpleGraph.dist_le q).trans_eq (hq.trans hlen)
  · have hH := leaf_delete_connected G hconn v u hv hvu
    obtain ⟨q, _, hlen⟩ := (hH.preconnected a b).exists_path_of_dist
    have hh := SimpleGraph.dist_le (q.map (SimpleGraph.Embedding.induce (G := G) {x | x ≠ v}).toHom)
    simpa only [SimpleGraph.Walk.length_map, hlen] using hh

omit [DecidableEq V] in
/-- A leaf-to-retained distance is one plus the retained neighbor distance. -/
theorem leaf_distance (hconn : G.Connected) (v u : V) (hv : G.degree v = 1)
    (hvu : G.Adj v u) (j : {x : V // x ≠ v}) :
    G.dist v j.val = (G.induce {x | x ≠ v}).dist ⟨u, hvu.ne.symm⟩ j + 1 := by
  apply le_antisymm
  · have hH := leaf_delete_connected G hconn v u hv hvu
    obtain ⟨q, _, hlen⟩ := (hH.preconnected ⟨u, hvu.ne.symm⟩ j).exists_path_of_dist
    let qG := q.map (SimpleGraph.Embedding.induce (G := G) {x | x ≠ v}).toHom
    have hh := SimpleGraph.dist_le (qG.cons hvu)
    simpa only [SimpleGraph.Walk.length_cons, qG, SimpleGraph.Walk.length_map, hlen] using hh
  · obtain ⟨p, hp, hlen⟩ := (hconn.preconnected v j.val).exists_path_of_dist
    obtain ⟨w, hvw, p, rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne (Ne.symm j.property) p
    have hwu : w = u := (leaf_adj_iff G v u hv hvu w).mp hvw
    subst w
    obtain ⟨q, hq⟩ := leaf_path_delete G v u hv hvu p hp.of_cons hvu.ne.symm j.property
    have hh := SimpleGraph.dist_le q
    change (G.induce {x | x ≠ v}).dist ⟨u, hvu.ne.symm⟩ j ≤ q.length at hh
    rw [hq] at hh
    simp only [SimpleGraph.Walk.length_cons] at hlen
    omega

/-- Exact cardinality lost by deleting one actual vertex. -/
theorem delete_vertex_card (v : V) : Fintype.card {x : V // x ≠ v} + 1 = Fintype.card V := by
  have hh := Fintype.card_subtype_compl (fun x : V => x = v)
  simp only [Fintype.card_subtype_eq] at hh
  have hcard : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  simp only [← Nat.card_eq_fintype_card] at hh hcard ⊢
  change Nat.card {x : V // x ≠ v} = Nat.card V - 1 at hh
  omega

/-- Exact decomposition of an arbitrary finite sum around the deleted vertex. -/
theorem sum_delete_vertex_add (v : V) (f : V → ℕ) :
    (∑ i : {x : V // x ≠ v}, f i.val) + f v = ∑ x, f x := by
  have hh : (∑ i : {x : V // x ≠ v}, f i.val) = ∑ x ∈ Finset.univ.erase v, f x :=
    (Finset.sum_subtype (Finset.univ.erase v) (by simp [ne_comm]) f).symm
  rw [hh]
  exact Finset.sum_erase_add _ _ (Finset.mem_univ v)

/-- Leaf deletion preserves degree balance exactly. -/
theorem leaf_delete_degree_sum (hsum : (∑ v, G.degree v) = 2 * Fintype.card V)
    (v u : V) (hv : G.degree v = 1) (hvu : G.Adj v u) :
    (∑ i : {x : V // x ≠ v}, (G.induce {x | x ≠ v}).degree i) =
      2 * Fintype.card {x : V // x ≠ v} := by
  have hsumdel := congrArg (fun f : {x : V // x ≠ v} → ℕ => ∑ i, f i)
    (funext (degree_delete_vertex G v))
  dsimp only at hsumdel
  rw [Finset.sum_add_distrib] at hsumdel
  have hneighbor : (∑ i : {x : V // x ≠ v}, if G.Adj i.val v then 1 else 0) = 1 := by
    have hadj : ∀ i : {x : V // x ≠ v}, G.Adj i.val v ↔ i = ⟨u, hvu.ne.symm⟩ := by
      intro i
      rw [G.adj_comm, leaf_adj_iff G v u hv hvu]
      constructor
      · intro h; apply Subtype.ext; exact h
      · intro h; exact congrArg Subtype.val h
    simp only [hadj, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hneighbor] at hsumdel
  have hsumall := sum_delete_vertex_add v (fun x => G.degree x)
  rw [hv, hsum] at hsumall
  have hcard := delete_vertex_card v
  omega

/-- The actual induced remaining graph retains cyclomatic number one. -/
theorem leaf_delete_excess (hconn : G.Connected) (hexcess : graphExcess G = 1)
    (v u : V) (hv : G.degree v = 1) (hvu : G.Adj v u) :
    graphExcess (G.induce {x | x ≠ v}) = 1 := by
  have hH := leaf_delete_connected G hconn v u hv hvu
  have hbalance := leaf_delete_degree_sum G (unicyclic_degree_sum G hconn hexcess) v u hv hvu
  have hhand := (G.induce {x | x ≠ v}).sum_degrees_eq_twice_card_edges
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hbalance hhand
  have hhand' : 2 * Nat.card {x : V // x ≠ v} = 2 * (G.induce {x | x ≠ v}).edgeFinset.card := by
    calc
      _ = ∑ x : {x : V // x ≠ v}, Nat.card ((G.induce {x | x ≠ v}).neighborSet x) := hbalance.symm
      _ = _ := by convert hhand using 1
  clear hhand

  have hedges : (G.induce {x | x ≠ v}).edgeFinset.card = Nat.card (G.induce {x | x ≠ v}).edgeSet := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
  rw [hedges] at hhand'
  have heq : Nat.card (G.induce {x | x ≠ v}).edgeSet = Nat.card {x : V // x ≠ v} := by omega
  unfold graphExcess
  rw [connected_component_card _ hH]
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  change Nat.card (G.induce {x | x ≠ v}).edgeSet + 1 - Nat.card {x : V // x ≠ v} = 1
  rw [heq]
  omega

end FiniteGraph
end
end LocalLaw
