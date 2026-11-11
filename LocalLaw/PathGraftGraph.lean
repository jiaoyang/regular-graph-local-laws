import Mathlib

/-!
# Canonical finite path grafts

A path of ell fresh vertices is attached to one old vertex. Both the sum
indexing and the canonical Fin(n+ell) indexing are concrete finite graphs.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance pathGraftDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Old vertices and fresh path vertices remain distinguished by a sum type. -/
def pathGraftSum {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (ell : ℕ) :
    SimpleGraph (Fin n ⊕ Fin ell) where
  Adj
    | Sum.inl a, Sum.inl b => G.Adj a b
    | Sum.inl a, Sum.inr b => a = v ∧ b.val = 0
    | Sum.inr a, Sum.inl b => b = v ∧ a.val = 0
    | Sum.inr a, Sum.inr b => a.val + 1 = b.val ∨ b.val + 1 = a.val
  symm := by
    intro a b h
    cases a <;> cases b
    · exact h.symm
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    intro a
    cases a with
    | inl a => exact G.loopless a
    | inr a => dsimp; omega

/-- The canonical graph labels preserve all old labels and put fresh labels
at n,n+1,...,n+ell-1. -/
def pathGraftGraph {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (ell : ℕ) :
    SimpleGraph (Fin (n + ell)) :=
  (pathGraftSum G v ell).comap finSumFinEquiv.symm

/-- Exact identification of the two concrete indexing conventions. -/
def pathGraftIso {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (ell : ℕ) :
    pathGraftSum G v ell ≃g pathGraftGraph G v ell where
  toEquiv := finSumFinEquiv
  map_rel_iff' := by intro a b; simp only [pathGraftGraph, SimpleGraph.comap_adj, Equiv.symm_apply_apply]

/-- The old graft vertex is returned when ell=0; otherwise the last new label. -/
def pathGraftEndpoint {n : ℕ} (v : Fin n) (ell : ℕ) : Fin (n + ell) :=
  if h : ell = 0 then h ▸ v.castAdd 0 else Fin.natAdd n ⟨ell - 1, by omega⟩

/-- Old vertices embed as their original graph. -/
def pathGraftOldEmbedding {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (ell : ℕ) :
    G ↪g pathGraftSum G v ell where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Iff.rfl

/-- Fresh path adjacencies are literal successor adjacencies. -/
def pathGraftFreshEmbedding {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (ell : ℕ) :
    SimpleGraph.pathGraph ell ↪g pathGraftSum G v ell where
  toFun := Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := by intro a b; exact SimpleGraph.pathGraph_adj.symm

/-- Every fresh vertex is reachable from the old graft vertex. -/
theorem pathGraftSum_connected {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (ell : ℕ)
    (hG : G.Connected) : (pathGraftSum G v ell).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨Sum.inl v, ?_⟩
  intro a
  cases a with
  | inl a => exact (hG.preconnected v a).map (pathGraftOldEmbedding G v ell).toHom
  | inr a =>
    let zero : Fin ell := ⟨0, lt_of_le_of_lt (Nat.zero_le a.val) a.is_lt⟩
    have hedge : (pathGraftSum G v ell).Adj (Sum.inl v) (Sum.inr zero) := ⟨rfl, rfl⟩
    exact hedge.reachable.trans
      (((SimpleGraph.pathGraph_preconnected ell) zero a).map (pathGraftFreshEmbedding G v ell).toHom)

/-- Counting a possible fresh successor. -/
theorem sum_fin_successor_indicator (ell : ℕ) (i : Fin ell) :
    (∑ j : Fin ell, if i.val + 1 = j.val then (1 : ℕ) else 0) =
      if i.val + 1 < ell then 1 else 0 := by
  by_cases h : i.val + 1 < ell
  · have heq : ∀ j : Fin ell, (i.val + 1 = j.val) ↔ j = ⟨i.val + 1, h⟩ := by
      intro j
      constructor
      · intro hj; apply Fin.ext; exact hj.symm
      · intro hj; exact (congrArg Fin.val hj).symm
    simp only [heq, if_pos h, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have heq : ∀ j : Fin ell, ¬i.val + 1 = j.val := by intro j hj; omega
    simp only [heq, if_false, Finset.sum_const_zero, if_neg h]

/-- Counting a possible fresh predecessor. -/
theorem sum_fin_predecessor_indicator (ell : ℕ) (i : Fin ell) :
    (∑ j : Fin ell, if j.val + 1 = i.val then (1 : ℕ) else 0) =
      if 0 < i.val then 1 else 0 := by
  by_cases h : 0 < i.val
  · let j₀ : Fin ell := ⟨i.val - 1, by omega⟩
    have heq : ∀ j : Fin ell, (j.val + 1 = i.val) ↔ j = j₀ := by
      intro j
      constructor
      · intro hj; apply Fin.ext; dsimp [j₀]; omega
      · intro hj; have hv := congrArg Fin.val hj; dsimp [j₀] at hv; omega
    simp only [heq, if_pos h, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have heq : ∀ j : Fin ell, ¬j.val + 1 = i.val := by intro j hj; omega
    simp only [heq, if_false, Finset.sum_const_zero, if_neg h]

/-- The old degree changes only at the graft vertex, when a path is added. -/
theorem pathGraftSum_degree_old {n : ℕ} (G : SimpleGraph (Fin n)) (v x : Fin n) (ell : ℕ) :
    (pathGraftSum G v ell).degree (Sum.inl x) = G.degree x + (if x = v ∧ 0 < ell then 1 else 0) := by
  have hsum := (pathGraftSum G v ell).degree_eq_sum_if_adj (R := ℕ) (Sum.inl x)
  rw [Fintype.sum_sum_type] at hsum
  simp only [Nat.cast_id] at hsum
  conv_rhs at hsum => simp only [pathGraftSum]
  rw [← G.degree_eq_sum_if_adj (R := ℕ) x] at hsum
  norm_num only [Nat.cast_id] at hsum
  rw [hsum]
  congr 1
  by_cases hx : x = v
  · subst x
    cases ell with
    | zero => simp
    | succ ell =>
      have heq : ∀ j : Fin (ell + 1), j.val = 0 ↔ j = 0 := by intro j; exact Fin.val_eq_zero_iff
      simp only [true_and, heq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Nat.zero_lt_succ, and_self]
  · simp [hx]

/-- Every fresh interior vertex has degree two; the final fresh vertex has
one neighbor. The initial fresh vertex includes its old attachment edge. -/
theorem pathGraftSum_degree_fresh {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (ell : ℕ) (i : Fin ell) :
    (pathGraftSum G v ell).degree (Sum.inr i) = if i.val + 1 = ell then 1 else 2 := by
  have hsum := (pathGraftSum G v ell).degree_eq_sum_if_adj (R := ℕ) (Sum.inr i)
  rw [Fintype.sum_sum_type] at hsum
  simp only [Nat.cast_id] at hsum
  conv_rhs at hsum => simp only [pathGraftSum]
  have hold : (∑ j : Fin n, if j = v ∧ i.val = 0 then (1 : ℕ) else 0) = if i.val = 0 then 1 else 0 := by
    by_cases hi : i.val = 0 <;> simp [hi]
  have hsplit : ∀ j : Fin ell,
      (if i.val + 1 = j.val ∨ j.val + 1 = i.val then (1 : ℕ) else 0) =
        (if i.val + 1 = j.val then 1 else 0) + (if j.val + 1 = i.val then 1 else 0) := by
    intro j
    by_cases h₁ : i.val + 1 = j.val <;> by_cases h₂ : j.val + 1 = i.val <;> simp [h₁, h₂]
    omega
  have hsum' : (pathGraftSum G v ell).degree (Sum.inr i) =
      (∑ j : Fin n, if j = v ∧ i.val = 0 then (1 : ℕ) else 0) +
        (∑ j : Fin ell, if i.val + 1 = j.val ∨ j.val + 1 = i.val then (1 : ℕ) else 0) := by
    convert hsum using 1
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> split_ifs <;> rfl
  clear hsum
  have hsum := hsum'
  rw [hold] at hsum
  simp_rw [hsplit] at hsum
  rw [Finset.sum_add_distrib, sum_fin_successor_indicator, sum_fin_predecessor_indicator] at hsum
  split_ifs at hsum ⊢ <;> omega

/-- The fresh path contributes two degrees per new vertex after the single
old attachment contribution is included. -/
theorem pathGraftSum_fresh_degree_sum {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (ell : ℕ) :
    (∑ i : Fin ell, (pathGraftSum G v ell).degree (Sum.inr i)) + (if 0 < ell then 1 else 0) = 2 * ell := by
  cases ell with
  | zero => simp
  | succ ell =>
    rw [Fin.sum_univ_castSucc]
    have hinterior : ∀ i : Fin ell, (pathGraftSum G v (ell + 1)).degree (Sum.inr i.castSucc) = 2 := by
      intro i
      rw [pathGraftSum_degree_fresh, if_neg (by change i.val + 1 ≠ ell + 1; have hi := i.is_lt; omega)]
    simp only [hinterior, pathGraftSum_degree_fresh, Fin.val_last, if_pos rfl,
      Nat.zero_lt_succ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, ite_true]
    omega

/-- Exact number of edges introduced by the canonical path. -/
theorem pathGraftSum_edge_card {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (ell : ℕ) :
    (pathGraftSum G v ell).edgeFinset.card = G.edgeFinset.card + ell := by
  have hnew := (pathGraftSum G v ell).sum_degrees_eq_twice_card_edges
  have hold := G.sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_sum_type] at hnew
  have hsumold : (∑ x : Fin n, (pathGraftSum G v ell).degree (Sum.inl x)) =
      (∑ x : Fin n, G.degree x) + (if 0 < ell then 1 else 0) := by
    simp_rw [pathGraftSum_degree_old]
    rw [Finset.sum_add_distrib]
    congr 1
    by_cases h : 0 < ell <;> simp [h]
  rw [hsumold] at hnew
  have hfresh := pathGraftSum_fresh_degree_sum G v ell
  omega

/-- Adding a fresh pendant path preserves actual tree structure. -/
theorem pathGraftSum_isTree {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (ell : ℕ)
    (hG : G.IsTree) : (pathGraftSum G v ell).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨pathGraftSum_connected G v ell hG.isConnected, ?_⟩
  have hold := hG.card_edgeFinset
  have hnew := pathGraftSum_edge_card G v ell
  simp only [Fintype.card_fin] at hold
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
    Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  omega

/-- Actual connectedness on the canonical Fin labels. -/
theorem pathGraftGraph_connected {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (ell : ℕ)
    (hG : G.Connected) : (pathGraftGraph G v ell).Connected :=
  (pathGraftIso G v ell).connected_iff.mp (pathGraftSum_connected G v ell hG)

/-- Actual tree preservation on the canonical Fin labels. -/
theorem pathGraftGraph_isTree {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (ell : ℕ)
    (hG : G.IsTree) : (pathGraftGraph G v ell).IsTree := by
  have hsum := pathGraftSum_isTree G v ell hG
  refine ⟨pathGraftGraph_connected G v ell hG.isConnected, ?_⟩
  intro a p hp
  exact hsum.IsAcyclic (p.map (pathGraftIso G v ell).symm.toHom)
    (hp.map (pathGraftIso G v ell).symm.injective)

/-- Edge count in the exact canonical labeling used by finite pattern counts. -/
theorem pathGraftGraph_edge_card {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (ell : ℕ) :
    (pathGraftGraph G v ell).edgeFinset.card = G.edgeFinset.card + ell := by
  rw [← (pathGraftIso G v ell).card_edgeFinset_eq]
  exact pathGraftSum_edge_card G v ell

/-- Exact old degree formula on the canonical old injection Fin.castAdd. -/
theorem pathGraftGraph_degree_old {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (ell : ℕ) (x : Fin n) :
    (pathGraftGraph G v ell).degree (Fin.castAdd ell x) = G.degree x + (if x = v ∧ 0 < ell then 1 else 0) := by
  have hh := Fintype.card_congr ((pathGraftIso G v ell).mapNeighborSet (Sum.inl x))
  simp only [SimpleGraph.card_neighborSet_eq_degree] at hh
  change (pathGraftSum G v ell).degree (Sum.inl x) =
    (pathGraftGraph G v ell).degree (finSumFinEquiv (Sum.inl x)) at hh
  rw [finSumFinEquiv_apply_left] at hh
  exact hh.symm.trans (pathGraftSum_degree_old G v x ell)

/-- Exact fresh degree formula on Fin.natAdd. -/
theorem pathGraftGraph_degree_fresh {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (ell : ℕ) (i : Fin ell) :
    (pathGraftGraph G v ell).degree (Fin.natAdd n i) = if i.val + 1 = ell then 1 else 2 := by
  have hh := Fintype.card_congr ((pathGraftIso G v ell).mapNeighborSet (Sum.inr i))
  simp only [SimpleGraph.card_neighborSet_eq_degree] at hh
  change (pathGraftSum G v ell).degree (Sum.inr i) =
    (pathGraftGraph G v ell).degree (finSumFinEquiv (Sum.inr i)) at hh
  rw [finSumFinEquiv_apply_right] at hh
  exact hh.symm.trans (pathGraftSum_degree_fresh G v ell i)

/-- Away from the graft point every old degree is unchanged. -/
theorem pathGraftGraph_degree_old_of_ne {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (ell : ℕ)
    (x : Fin n) (hx : x ≠ v) :
    (pathGraftGraph G v ell).degree (Fin.castAdd ell x) = G.degree x := by
  rw [pathGraftGraph_degree_old, if_neg (by tauto), add_zero]

@[simp] theorem pathGraftEndpoint_zero {n : ℕ} (v : Fin n) :
    pathGraftEndpoint v 0 = Fin.castAdd 0 v := by simp [pathGraftEndpoint]

theorem pathGraftEndpoint_positive {n : ℕ} (v : Fin n) (ell : ℕ) (hell : 0 < ell) :
    pathGraftEndpoint v ell = Fin.natAdd n ⟨ell - 1, by omega⟩ := by
  simp only [pathGraftEndpoint, dif_neg (Nat.ne_zero_of_lt hell)]

/-- An actual nonempty graft always ends at a degree-one new vertex. -/
theorem pathGraftGraph_degree_endpoint {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (ell : ℕ)
    (hell : 0 < ell) : (pathGraftGraph G v ell).degree (pathGraftEndpoint v ell) = 1 := by
  rw [pathGraftEndpoint_positive v ell hell, pathGraftGraph_degree_fresh, if_pos (by change ell - 1 + 1 = ell; omega)]

/-- The only fresh endpoint label is the last fresh index. -/
theorem pathGraftEndpoint_fresh_iff {n : ℕ} (v : Fin n) (ell : ℕ) (i : Fin ell) :
    Fin.natAdd n i = pathGraftEndpoint v ell ↔ i.val + 1 = ell := by
  have hell : 0 < ell := lt_of_le_of_lt (Nat.zero_le i.val) i.is_lt
  rw [pathGraftEndpoint_positive v ell hell]
  constructor
  · intro h
    have hh := congrArg Fin.val h
    change n + i.val = n + (ell - 1) at hh
    omega
  · intro h
    apply Fin.ext
    change n + i.val = n + (ell - 1)
    omega

/-- Literal old-old adjacency is preserved by the canonical old injection. -/
theorem pathGraftGraph_adj_old {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (ell : ℕ) (i j : Fin n) :
    (pathGraftGraph G v ell).Adj (Fin.castAdd ell i) (Fin.castAdd ell j) ↔ G.Adj i j := by
  have hh := (pathGraftIso G v ell).map_rel_iff' (a := Sum.inl i) (b := Sum.inl j)
  simpa only [pathGraftIso, finSumFinEquiv_apply_left] using hh

/-- Every fresh vertex except the tracked endpoint has degree two. -/
theorem pathGraftGraph_degree_fresh_of_ne_endpoint {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (ell : ℕ) (i : Fin ell) (hi : Fin.natAdd n i ≠ pathGraftEndpoint v ell) :
    (pathGraftGraph G v ell).degree (Fin.natAdd n i) = 2 := by
  rw [pathGraftGraph_degree_fresh, if_neg]
  exact fun h => hi ((pathGraftEndpoint_fresh_iff v ell i).mpr h)

section FreshPathEmbedding
variable {n ell : ℕ} {V : Type*} {T : SimpleGraph V}
variable (G : SimpleGraph (Fin n)) (v : Fin n) (e : Fin n ↪ V) {w : V}
variable (p : T.Walk (e v) w) (hp : p.IsPath) (hlen : p.length = ell)
variable (hfresh : ∀ k : Fin ell, p.getVert (k.val + 1) ∉ Set.range e)

/-- An actual fresh simple path extends the old injection on the sum labels. -/
def pathGraftSumEmbedding : (Fin n ⊕ Fin ell) ↪ V where
  toFun := Sum.elim e (fun k => p.getVert (k.val + 1))
  inj' := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (e.injective hab)
      | inr b => exact False.elim (hfresh b ⟨a, hab⟩)
    | inr a =>
      cases b with
      | inl b => exact False.elim (hfresh a ⟨b, hab.symm⟩)
      | inr b =>
        have ha : a.val + 1 ≤ p.length := by have hh := a.is_lt; omega
        have hb : b.val + 1 ≤ p.length := by have hh := b.is_lt; omega
        have hh := hp.getVert_injOn ha hb hab
        exact congrArg Sum.inr (Fin.ext (by omega))

/-- The same genuine injection on the canonical Fin(n+ell) labels. -/
def pathGraftEmbedding : Fin (n + ell) ↪ V :=
  finSumFinEquiv.symm.toEmbedding.trans (pathGraftSumEmbedding v e p hp hlen hfresh)

@[simp] theorem pathGraftEmbedding_old (i : Fin n) :
    pathGraftEmbedding v e p hp hlen hfresh (Fin.castAdd ell i) = e i := by
  have hh : finSumFinEquiv.symm (Fin.castAdd ell i) = Sum.inl i := by
    rw [← finSumFinEquiv_apply_left, Equiv.symm_apply_apply]
  change pathGraftSumEmbedding v e p hp hlen hfresh (finSumFinEquiv.symm (Fin.castAdd ell i)) = e i
  rw [hh]
  rfl

@[simp] theorem pathGraftEmbedding_fresh (i : Fin ell) :
    pathGraftEmbedding v e p hp hlen hfresh (Fin.natAdd n i) = p.getVert (i.val + 1) := by
  have hh : finSumFinEquiv.symm (Fin.natAdd n i) = Sum.inr i := by
    rw [← finSumFinEquiv_apply_right, Equiv.symm_apply_apply]
  change pathGraftSumEmbedding v e p hp hlen hfresh (finSumFinEquiv.symm (Fin.natAdd n i)) = _
  rw [hh]
  rfl

/-- The tracked canonical endpoint is exactly the actual path endpoint. -/
theorem pathGraftEmbedding_endpoint :
    pathGraftEmbedding v e p hp hlen hfresh (pathGraftEndpoint v ell) = w := by
  cases ell with
  | zero =>
    rw [pathGraftEndpoint_zero, pathGraftEmbedding_old]
    calc
      e v = p.getVert 0 := p.getVert_zero.symm
      _ = w := by rw [← hlen, p.getVert_length]
  | succ ell =>
    rw [pathGraftEndpoint_positive v (ell + 1) (by omega), pathGraftEmbedding_fresh]
    change p.getVert ((ell + 1) - 1 + 1) = w
    rw [show (ell + 1) - 1 + 1 = ell + 1 by omega, ← hlen, p.getVert_length]

/-- The constructed injection maps every canonical graft edge to an actual
edge, whenever the old injection already preserves old graph edges. -/
theorem pathGraftEmbedding_adj
    (he : ∀ i j, G.Adj i j → T.Adj (e i) (e j)) (i j : Fin (n + ell))
    (hij : (pathGraftGraph G v ell).Adj i j) :
    T.Adj (pathGraftEmbedding v e p hp hlen hfresh i) (pathGraftEmbedding v e p hp hlen hfresh j) := by
  have hsum : ∀ a b : Fin n ⊕ Fin ell, (pathGraftSum G v ell).Adj a b →
      T.Adj (pathGraftSumEmbedding v e p hp hlen hfresh a) (pathGraftSumEmbedding v e p hp hlen hfresh b) := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact he a b hab
      | inr b =>
        rcases hab with ⟨rfl, hb⟩
        have hpos : 0 < p.length := by have hh := b.is_lt; omega
        have hh := p.adj_getVert_succ hpos
        simpa only [pathGraftSumEmbedding, Function.Embedding.coeFn_mk, Sum.elim_inl, Sum.elim_inr,
          p.getVert_zero, hb, zero_add] using hh
    | inr a =>
      cases b with
      | inl b =>
        rcases hab with ⟨rfl, ha⟩
        have hpos : 0 < p.length := by have hh := a.is_lt; omega
        have hh := (p.adj_getVert_succ hpos).symm
        simpa only [pathGraftSumEmbedding, Function.Embedding.coeFn_mk, Sum.elim_inl, Sum.elim_inr,
          p.getVert_zero, ha, zero_add] using hh
      | inr b =>
        rcases hab with hab | hba
        · have hpos : a.val + 1 < p.length := by have hh := b.is_lt; omega
          have hh := p.adj_getVert_succ hpos
          change T.Adj (p.getVert (a.val + 1)) (p.getVert (b.val + 1))
          convert hh using 1
          congr 1
          omega
        · have hpos : b.val + 1 < p.length := by have hh := a.is_lt; omega
          have hh := (p.adj_getVert_succ hpos).symm
          change T.Adj (p.getVert (a.val + 1)) (p.getVert (b.val + 1))
          convert hh using 1
          congr 1
          omega
  exact hsum (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) hij

end FreshPathEmbedding

end
end LocalLaw
