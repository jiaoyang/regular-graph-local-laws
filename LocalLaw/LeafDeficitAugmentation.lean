import LocalLaw.GoodThresholdOne

/-!
# Attaching one actual leaf consumes one source deficit

The new leaf has deficit zero and the chosen old positive deficit decreases
by one. The actual degree budgets, deficit mass, excess, and finite reference
principal matrix are proved, implementing the finite mechanism of Remark 2.8.
-/

open scoped BigOperators Matrix
namespace LocalLaw
noncomputable section
local instance leafDeficitDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section FiniteGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- One new leaf, attached to the old vertex v. -/
def leafAugmentGraph (v : V) : SimpleGraph (V ⊕ Unit) where
  Adj
    | Sum.inl a, Sum.inl b => G.Adj a b
    | Sum.inl a, Sum.inr _ => a = v
    | Sum.inr _, Sum.inl b => b = v
    | Sum.inr _, Sum.inr _ => False
  symm := by intro a b h; cases a <;> cases b <;> first | exact h.symm | exact h
  loopless := by intro a; cases a; exact G.loopless _; exact id

theorem leafAugmentGraph_degree_old (v x : V) :
    (leafAugmentGraph G v).degree (Sum.inl x) = G.degree x + (if x = v then 1 else 0) := by
  have hh := (leafAugmentGraph G v).degree_eq_sum_if_adj (R := ℕ) (Sum.inl x)
  rw [Fintype.sum_sum_type] at hh
  simp only [Nat.cast_id] at hh
  conv_rhs at hh => simp only [leafAugmentGraph]
  rw [← G.degree_eq_sum_if_adj (R := ℕ) x] at hh
  by_cases hx : x = v
  · simpa only [Nat.cast_id, Fintype.sum_unique, if_pos hx, ite_true] using hh
  · simpa only [Nat.cast_id, Fintype.sum_unique, if_neg hx, ite_false] using hh

theorem leafAugmentGraph_degree_new (v : V) :
    (leafAugmentGraph G v).degree (Sum.inr ()) = 1 := by
  have hh := (leafAugmentGraph G v).degree_eq_sum_if_adj (R := ℕ) (Sum.inr ())
  rw [Fintype.sum_sum_type] at hh
  simp only [Nat.cast_id] at hh
  conv_rhs at hh => simp only [leafAugmentGraph]
  simp only [if_false, Finset.sum_const_zero, add_zero] at hh
  have hh' : (leafAugmentGraph G v).degree (Sum.inr ()) = ∑ x : V, if x = v then (1 : ℕ) else 0 := by
    convert hh using 1
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> rfl
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true] using hh'

omit [Fintype V] [DecidableEq V] in

theorem leafAugmentGraph_connected (v : V) (hG : G.Connected) : (leafAugmentGraph G v).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨Sum.inl v, ?_⟩
  intro a
  cases a with
  | inl a =>
    let f : G →g leafAugmentGraph G v := { toFun := Sum.inl, map_rel' := fun h => h }
    exact (hG.preconnected v a).map f
  | inr a => exact (show (leafAugmentGraph G v).Adj (Sum.inl v) (Sum.inr a) from rfl).reachable

theorem leafAugmentGraph_edge_card (v : V) :
    (leafAugmentGraph G v).edgeFinset.card = G.edgeFinset.card + 1 := by
  have hh := (leafAugmentGraph G v).sum_degrees_eq_twice_card_edges
  have hG := G.sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_sum_type] at hh
  simp_rw [leafAugmentGraph_degree_old] at hh
  rw [Finset.sum_add_distrib] at hh
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Fintype.sum_unique,
    leafAugmentGraph_degree_new] at hh
  rw [show (default : Unit) = () from Subsingleton.elim _ _, leafAugmentGraph_degree_new] at hh
  omega

theorem leafAugmentGraph_excess (v : V) (hG : G.Connected) :
    graphExcess (leafAugmentGraph G v) = graphExcess G := by
  have hconn := leafAugmentGraph_connected G v hG
  have hnew := connected_graph_excess_euler (leafAugmentGraph G v) hconn
  have hold := connected_graph_excess_euler G hG
  have hcard := leafAugmentGraph_edge_card G v
  simp only [graphEdgeCount, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
    Fintype.card_sum, Fintype.card_unique] at hnew hold
  omega

/-- Removing the newly adjoined vertex gives an actual graph isomorphism
from the original graph onto the retained induced graph. -/
def leafAugmentDeleteIso (v : V) :
    G ≃g (leafAugmentGraph G v).induce {x | x ≠ Sum.inr ()} where
  toEquiv :=
    { toFun := fun x => ⟨Sum.inl x, by intro h; cases h⟩
      invFun := fun x => by
        cases hx : x.val with
        | inl a => exact a
        | inr a => exact False.elim (x.property (by cases a; exact hx))
      left_inv := fun _ => rfl
      right_inv := by
        intro x
        cases x with
        | mk x hx =>
          cases x with
          | inl x => rfl
          | inr x => cases x; exact False.elim (hx rfl) }
  map_rel_iff' := Iff.rfl

/-- Old intrinsic graph distances are unchanged by the added pendant leaf. -/
theorem leafAugmentGraph_distance_old (v : V) (hG : G.Connected) (i j : V) :
    (leafAugmentGraph G v).dist (Sum.inl i) (Sum.inl j) = G.dist i j := by
  let H := leafAugmentGraph G v
  have hconn := leafAugmentGraph_connected G v hG
  have hleaf : H.degree (Sum.inr ()) = 1 := leafAugmentGraph_degree_new G v
  have hadj : H.Adj (Sum.inr ()) (Sum.inl v) := rfl
  have hdel := leaf_delete_distance H hconn (Sum.inr ()) (Sum.inl v) hleaf hadj
    ⟨Sum.inl i, by intro h; cases h⟩ ⟨Sum.inl j, by intro h; cases h⟩
  have hiso := graphIso_distance (leafAugmentDeleteIso G v) ((leafAugmentDeleteIso G v).connected_iff.mp hG) i j
  exact hdel.symm.trans hiso.symm

/-- Distance from the added leaf to any old vertex is one plus its old-root
distance in the original actual graph. -/
theorem leafAugmentGraph_distance_new (v : V) (hG : G.Connected) (j : V) :
    (leafAugmentGraph G v).dist (Sum.inr ()) (Sum.inl j) = G.dist v j + 1 := by
  let H := leafAugmentGraph G v
  have hconn := leafAugmentGraph_connected G v hG
  have hleaf : H.degree (Sum.inr ()) = 1 := leafAugmentGraph_degree_new G v
  have hadj : H.Adj (Sum.inr ()) (Sum.inl v) := rfl
  have hdist := leaf_distance H hconn (Sum.inr ()) (Sum.inl v) hleaf hadj ⟨Sum.inl j, by intro h; cases h⟩
  have hiso := graphIso_distance (leafAugmentDeleteIso G v) ((leafAugmentDeleteIso G v).connected_iff.mp hG) v j
  exact hdist.trans (congrArg (fun n => n + 1) hiso.symm)

end FiniteGraph

namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

/-- Genuine source deficit after attaching the new leaf. -/
def attachLeaf (g : DeficientGraph V d) (hd : 1 ≤ d) (v : V) (hv : 0 < g.deficit v) :
    DeficientGraph (V ⊕ Unit) d where
  graph := leafAugmentGraph g.graph v
  deficit := Sum.elim (fun x => g.deficit x - (if x = v then 1 else 0)) (fun _ => 0)
  degree_deficit_le := by
    intro x
    cases x with
    | inl x =>
      rw [leafAugmentGraph_degree_old]
      by_cases hx : x = v
      · subst x
        simp only [if_pos rfl, ite_true, Sum.elim_inl]
        have hh := g.degree_deficit_le v
        omega
      · simpa only [if_neg hx, Sum.elim_inl, Nat.sub_zero, add_zero] using g.degree_deficit_le x
    | inr x =>
      cases x
      simp only [leafAugmentGraph_degree_new, Sum.elim_inr, add_zero]
      exact hd

/-- Total desired missing degree at every old vertex is preserved. -/
theorem attachLeaf_degree_deficit (g : DeficientGraph V d) (hd : 1 ≤ d) (v : V) (hv : 0 < g.deficit v) (x : V) :
    (g.attachLeaf hd v hv).graph.degree (Sum.inl x) + (g.attachLeaf hd v hv).deficit (Sum.inl x) =
      g.graph.degree x + g.deficit x := by
  simp only [attachLeaf, leafAugmentGraph_degree_old, Sum.elim_inl]
  by_cases hx : x = v
  · subst x; simp only [if_pos rfl, ite_true]; omega
  · simp only [if_neg hx, add_zero, Nat.sub_zero]

/-- The total deficit decreases by exactly one. -/
theorem attachLeaf_deficit_sum (g : DeficientGraph V d) (hd : 1 ≤ d) (v : V) (hv : 0 < g.deficit v) :
    (∑ x, (g.attachLeaf hd v hv).deficit x) + 1 = ∑ x, g.deficit x := by
  rw [Fintype.sum_sum_type]
  simp only [attachLeaf, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, add_zero]
  have hpoint : ∀ x, (g.deficit x - (if x = v then 1 else 0)) + (if x = v then 1 else 0) = g.deficit x := by
    intro x
    by_cases hx : x = v
    · subst x; simp only [if_pos rfl, ite_true]; omega
    · simp only [if_neg hx, Nat.sub_zero, add_zero]
  have hh := congrArg (fun f : V → ℕ => ∑ x, f x) (funext hpoint)
  dsimp only at hh
  rw [Finset.sum_add_distrib] at hh
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true] using hh

/-- Connectedness and excess are preserved by the actual attachment. -/
theorem attachLeaf_excess (g : DeficientGraph V d) (hd : 1 ≤ d) (v : V) (hv : 0 < g.deficit v)
    (hconn : g.graph.Connected) : graphExcess (g.attachLeaf hd v hv).graph = graphExcess g.graph :=
  leafAugmentGraph_excess g.graph v hconn

/-- Exact total-complexity reduction, including deficits bigger than one. -/
theorem attachLeaf_complexity (g : DeficientGraph V d) (hd : 1 ≤ d) (v : V) (hv : 0 < g.deficit v)
    (hconn : g.graph.Connected) :
    ((∑ x, (g.attachLeaf hd v hv).deficit x) + graphExcess (g.attachLeaf hd v hv).graph) + 1 =
      (∑ x, g.deficit x) + graphExcess g.graph := by
  rw [g.attachLeaf_excess hd v hv hconn]
  have hh := g.attachLeaf_deficit_sum hd v hv
  omega

/-- The original actual boundary coefficient is the retained coefficient of
the augmented graph; the decremented deficit offsets its added degree. -/
theorem attachLeaf_boundaryCoefficient (g : DeficientGraph V d) (hd : 1 ≤ d) (v : V)
    (hv : 0 < g.deficit v) (x : V) :
    (g.attachLeaf hd v hv).boundaryCoefficient (Sum.inl x) = g.boundaryCoefficient x := by
  have hh := g.attachLeaf_degree_deficit hd v hv x
  have hreal : ((g.attachLeaf hd v hv).graph.degree (Sum.inl x) : ℝ) +
      ((g.attachLeaf hd v hv).deficit (Sum.inl x) : ℝ) =
        (g.graph.degree x : ℝ) + (g.deficit x : ℝ) := by exact_mod_cast hh
  unfold boundaryCoefficient
  congr 1
  linarith

/-- Actual principal operator identification: deleting the new leaf yields
the original source model exactly, with the original deficit convention. -/
theorem attachLeaf_extensionMatrix_principal (g : DeficientGraph V d) (hd : 1 ≤ d) (v : V)
    (hv : 0 < g.deficit v) (w z : ℂ) :
    ((g.attachLeaf hd v hv).extensionMatrix w z).submatrix Sum.inl Sum.inl = g.extensionMatrix w z := by
  ext i j
  simp only [extensionMatrix, boundaryMatrix, spectralMatrix, H, boundaryDiagonal,
    Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, Matrix.diagonal_apply, Sum.inl.injEq]
  rw [g.attachLeaf_boundaryCoefficient hd v hv i]
  simp only [normalizedAdjacency, Matrix.smul_apply, smul_eq_mul, SimpleGraph.adjMatrix_apply,
    attachLeaf, leafAugmentGraph]

/-- Deleting the new leaf restores the original deficit at every retained
vertex, even if the old positive deficit was larger than one. -/
theorem attachLeaf_delete_deficit (g : DeficientGraph V d) (hd : 1 ≤ d) (v : V)
    (hv : 0 < g.deficit v) (x : V) :
    (g.attachLeaf hd v hv).deficit (Sum.inl x) +
      ((g.attachLeaf hd v hv).graph.degree (Sum.inl x) -
        ((g.attachLeaf hd v hv).graph.induce {a | a ≠ Sum.inr ()}).degree
          ⟨Sum.inl x, by intro h; cases h⟩) = g.deficit x := by
  have hdegdel : ((g.attachLeaf hd v hv).graph.induce {a | a ≠ Sum.inr ()}).degree
      ⟨Sum.inl x, by intro h; cases h⟩ = g.graph.degree x := by
    have hh := Fintype.card_congr ((leafAugmentDeleteIso g.graph v).mapNeighborSet x)
    simp only [SimpleGraph.card_neighborSet_eq_degree] at hh
    exact hh.symm
  change (g.deficit x - (if x = v then 1 else 0)) +
    ((leafAugmentGraph g.graph v).degree (Sum.inl x) -
      ((g.attachLeaf hd v hv).graph.induce {a | a ≠ Sum.inr ()}).degree ⟨Sum.inl x, by intro h; cases h⟩) = _
  rw [hdegdel, leafAugmentGraph_degree_old]
  by_cases hx : x = v
  · subst x; simp only [if_pos rfl, ite_true]; omega
  · simp only [if_neg hx, Nat.sub_zero, add_zero, Nat.sub_self]

end DeficientGraph
end
end LocalLaw
