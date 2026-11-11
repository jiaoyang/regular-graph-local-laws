import LocalLaw.ConnectedPartitionExcess
import LocalLaw.GeneralGraphEuler

/-!
# Excess of possibly disconnected connected-cell partitions

Every connected component contains a complete partition cell, so the true
component count is at most the number of cells. General Euler counting then
proves the same uniform excess bound without assuming graph connectivity.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance generalPartitionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V I : Type*} [Fintype V] [Fintype I]
theorem partition_excess_bound (G : SimpleGraph V)
    (f : V → I) (hcell : ∀ i, (G.induce {v | f v = i}).Connected)
    (ω κ : ℕ) (hbudget : ∀ i, graphExcess (G.induce {v | f v = i}) ≤ ω)
    (hcross : ∀ i j, i ≠ j → Nat.card (CellCrossEdge G {v | f v = i} {v | f v = j}) ≤ κ) :
    graphExcess G ≤ Nat.card I * ω + (Nat.card I) ^ 2 * κ := by
  have hcomponents : Nat.card G.ConnectedComponent ≤ Nat.card I := by
    let center (i : I) : {v : V // f v = i} := Classical.choice (hcell i).nonempty
    let F : I → G.ConnectedComponent := fun i => G.connectedComponentMk (center i).val
    have hF : Function.Surjective F := by
      intro C
      obtain ⟨v, hv⟩ := C.exists_rep
      refine ⟨f v, ?_⟩
      obtain ⟨p⟩ := (hcell (f v)).preconnected (center (f v)) ⟨v, rfl⟩
      have hh := SimpleGraph.ConnectedComponent.sound
        (p.map (SimpleGraph.Embedding.induce {w | f w = f v}).toHom).reachable
      exact hh.trans hv
    exact Nat.card_le_card_of_surjective F hF
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
  have hglobal := graph_excess_euler G
  nlinarith

end LocalLaw
