import LocalLaw.ConnectedCellCrossEdges

/-!
# An excess bound for actual connected vertex partitions

Finite oriented edges are partitioned by their endpoint labels. Exact Euler
identities in the connected cells cancel their vertex counts. Consequently a
uniform cell-excess bound and a uniform cross-edge bound give an excess bound
depending only on the number of cells.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance connectedPartitionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V I : Type*} [Fintype V] [Fintype I]

def DartCellFiber (G : SimpleGraph V) (f : V → I) (i j : I) :=
  {e : G.Dart // f e.fst = i ∧ f e.snd = j}

instance dartCellFiberFintype (G : SimpleGraph V) (f : V → I) (i j : I) : Fintype (DartCellFiber G f i j) := by
  unfold DartCellFiber
  infer_instance

def dartCellsEquiv (G : SimpleGraph V) (f : V → I) :
    G.Dart ≃ Σ i : I, Σ j : I, DartCellFiber G f i j where
  toFun e := ⟨f e.fst, f e.snd, ⟨e, rfl, rfl⟩⟩
  invFun p := p.2.2.val
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨i, j, e, hi, hj⟩
    cases hi
    cases hj
    rfl

def dartCellCrossEquiv (G : SimpleGraph V) (f : V → I) (i j : I) :
    DartCellFiber G f i j ≃ CellCrossEdge G {v | f v = i} {v | f v = j} where
  toFun e := ⟨e.val.toProd, e.val.adj, e.property.1, e.property.2⟩
  invFun e := ⟨⟨e.val, e.property.1⟩, e.property.2.1, e.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def dartCellDiagonalEquiv (G : SimpleGraph V) (f : V → I) (i : I) :
    DartCellFiber G f i i ≃ (G.induce {v | f v = i}).Dart where
  toFun e := ⟨(⟨e.val.fst, e.property.1⟩, ⟨e.val.snd, e.property.2⟩), e.val.adj⟩
  invFun e := ⟨⟨(e.fst.val, e.snd.val), e.adj⟩, e.fst.property, e.snd.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem connected_partition_excess_bound (G : SimpleGraph V) (hG : G.Connected)
    (f : V → I) (hcell : ∀ i, (G.induce {v | f v = i}).Connected)
    (ω κ : ℕ) (hbudget : ∀ i, graphExcess (G.induce {v | f v = i}) ≤ ω)
    (hcross : ∀ i j, i ≠ j → Nat.card (CellCrossEdge G {v | f v = i} {v | f v = j}) ≤ κ) :
    graphExcess G ≤ Nat.card I * ω + (Nat.card I) ^ 2 * κ := by
  letI : Nonempty I := ⟨f (Classical.choice hG.nonempty)⟩
  have hm : 1 ≤ Nat.card I := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos
  have hfiber : ∀ i j, Nat.card (DartCellFiber G f i j) ≤
      (if i = j then 2 * graphEdgeCount (G.induce {v | f v = i}) else 0) + κ := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl, Nat.card_congr (dartCellDiagonalEquiv G f i), graph_dart_count]
      omega
    · rw [if_neg hij, zero_add, Nat.card_congr (dartCellCrossEquiv G f i j)]
      exact hcross i j hij
  have hdarts : Nat.card G.Dart = ∑ i : I, ∑ j : I, Nat.card (DartCellFiber G f i j) := by
    have hh := Nat.card_congr (dartCellsEquiv G f)
    simpa only [Nat.card_sigma] using hh
  have hbound : 2 * graphEdgeCount G ≤
      2 * (∑ i : I, graphEdgeCount (G.induce {v | f v = i})) + (Nat.card I) ^ 2 * κ := by
    rw [← graph_dart_count G, hdarts]
    calc
      _ ≤ ∑ i : I, ∑ j : I,
          ((if i = j then 2 * graphEdgeCount (G.induce {v | f v = i}) else 0) + κ) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hfiber i j))
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, Nat.card_eq_fintype_card]
        simp only [Nat.cast_id]
        ring
  have hvertices : (∑ i : I, Nat.card {v : V // f v = i}) = Nat.card V := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv f)
  have heuler : (∑ i : I, graphExcess (G.induce {v | f v = i})) + Nat.card V =
      (∑ i : I, graphEdgeCount (G.induce {v | f v = i})) + Nat.card I := by
    rw [← hvertices, ← Finset.sum_add_distrib]
    have hh := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
      connected_graph_excess_euler (G.induce {v | f v = i}) (hcell i))
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, Nat.card_eq_fintype_card] using hh
  have hsum : (∑ i : I, graphExcess (G.induce {v | f v = i})) ≤ Nat.card I * ω := by
    exact (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) => hbudget i)).trans_eq
      (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card, Nat.cast_id])
  have hglobal := connected_graph_excess_euler G hG
  nlinarith

end LocalLaw
