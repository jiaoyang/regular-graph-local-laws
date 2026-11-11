import LocalLaw.ExcessCutset

/-!
# Count actual even-degree edge subgraphs by the excess

An even-degree subgraph is encoded by its edges outside an actual spanning
tree. Equality of codes makes the symmetric difference an even-degree forest,
which must be empty. The off-tree edge count is the connected graph's Euler
excess, so there are at most 2^excess such subgraphs, including the empty graph.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000

namespace LocalLaw

local instance cycleSpaceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section EvenGraphs

variable {V : Type*} [Fintype V]

def graphXor (A B : SimpleGraph V) : SimpleGraph V := (A \ B) ⊔ (B \ A)

/-- Degree identity behind parity of the actual symmetric difference. -/
theorem graphXor_degree_identity (A B : SimpleGraph V) (v : V) :
    (graphXor A B).degree v + 2 * (A ⊓ B).degree v = A.degree v + B.degree v := by
  let a := A.neighborFinset v
  let b := B.neighborFinset v
  have hx : (graphXor A B).neighborFinset v = (a \ b) ∪ (b \ a) := by
    ext w
    simp only [graphXor, a, b, SimpleGraph.mem_neighborFinset, Finset.mem_union,
      Finset.mem_sdiff, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]
  have hi : (A ⊓ B).neighborFinset v = a ∩ b := by
    ext w
    simp only [a, b, SimpleGraph.mem_neighborFinset, Finset.mem_inter, SimpleGraph.inf_adj]
  have hd : Disjoint (a \ b) (b \ a) := by
    apply Finset.disjoint_left.mpr
    intro w hw₁ hw₂
    exact (Finset.mem_sdiff.mp hw₁).2 (Finset.mem_sdiff.mp hw₂).1
  have ha := Finset.card_sdiff_add_card_inter a b
  have hb := Finset.card_sdiff_add_card_inter b a
  rw [Finset.inter_comm b a] at hb
  change ((graphXor A B).neighborFinset v).card +
    2 * ((A ⊓ B).neighborFinset v).card = a.card + b.card
  rw [hx, hi, Finset.card_union_of_disjoint hd]
  omega

theorem graphXor_even (A B : SimpleGraph V)
    (hA : ∀ v, Even (A.degree v)) (hB : ∀ v, Even (B.degree v)) :
    ∀ v, Even ((graphXor A B).degree v) := by
  intro v
  have hs : Even ((graphXor A B).degree v + 2 * (A ⊓ B).degree v) := by
    rw [graphXor_degree_identity]
    exact (hA v).add (hB v)
  exact (Nat.even_add.mp hs).mpr (even_two_mul _)

omit [Fintype V] in
theorem graph_acyclic_of_le {A B : SimpleGraph V} (hAB : A ≤ B) (hB : B.IsAcyclic) :
    A.IsAcyclic := by
  intro v p hp
  exact hB (p.mapLe hAB) (hp.mapLe hAB)

omit [Fintype V] in
theorem graph_acyclic_induce (H : SimpleGraph V) (S : Set V) (hH : H.IsAcyclic) :
    (H.induce S).IsAcyclic := by
  let f := SimpleGraph.Embedding.induce (G := H) S
  intro v p hp
  exact hH (p.map f.toHom) (hp.map f.injective)

theorem component_graph_degree (H : SimpleGraph V) (C : H.ConnectedComponent) (v : C.supp) :
    (H.induce C.supp).degree v = H.degree v.val := by
  apply SimpleGraph.degree_induce_of_neighborSet_subset
  intro w hw
  exact (C.mem_supp_congr_adj hw).mp v.property

theorem connected_degree_positive {W : Type*} [Fintype W] [Nontrivial W]
    (H : SimpleGraph W) (hH : H.Connected) (v : W) : 0 < H.degree v := by
  obtain ⟨w, hw⟩ := exists_ne v
  obtain ⟨p⟩ := hH v w
  cases p with
  | nil => exact (hw rfl).elim
  | @cons v u w h p => exact (H.degree_pos_iff_exists_adj v).mpr ⟨u, h⟩

/-- A finite acyclic graph with all degrees even has no edge. -/
theorem even_forest_eq_bot (H : SimpleGraph V) (hforest : H.IsAcyclic)
    (heven : ∀ v, Even (H.degree v)) : H = ⊥ := by
  by_contra hH
  have hex : ∃ a b, H.Adj a b := by
    by_contra hnone
    apply hH
    ext a b
    simp only [SimpleGraph.bot_adj, iff_false]
    exact fun hab => hnone ⟨a, b, hab⟩
  obtain ⟨a, b, hab⟩ := hex
  let C := H.connectedComponentMk a
  let K := H.induce C.supp
  let aC : C.supp := ⟨a, rfl⟩
  let bC : C.supp := ⟨b, SimpleGraph.ConnectedComponent.sound hab.symm.reachable⟩
  have habC : aC ≠ bC := fun h => hab.ne (congrArg Subtype.val h)
  letI : Nontrivial C.supp := ⟨⟨aC, bC, habC⟩⟩
  have hconn : K.Connected := SimpleGraph.ConnectedComponent.connected_induce_supp C
  have htree : K.IsTree := ⟨hconn, graph_acyclic_induce H C.supp hforest⟩
  have htwo : ∀ v : C.supp, 2 ≤ K.degree v := by
    intro v
    have hpos := connected_degree_positive K hconn v
    have he : Even (K.degree v) := by
      rw [component_graph_degree]
      exact heven v.val
    obtain ⟨n, hn⟩ := he
    omega
  have hsum : 2 * Fintype.card C.supp ≤ ∑ v : C.supp, K.degree v := by
    calc
      _ = ∑ _v : C.supp, 2 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v _ => htwo v)
  have hdegrees := K.sum_degrees_eq_twice_card_edges
  have hcard := htree.card_edgeFinset
  omega

end EvenGraphs

section EvenSubgraphCode

variable {V : Type*} [Fintype V]

/-- Actual spanning edge subgraphs of G with every vertex degree even. -/
def EvenEdgeSubgraph (G : SimpleGraph V) :=
  {C : SimpleGraph V // C ≤ G ∧ ∀ v, Even (C.degree v)}

instance evenEdgeSubgraphFintype (G : SimpleGraph V) : Fintype (EvenEdgeSubgraph G) := by
  unfold EvenEdgeSubgraph
  infer_instance

/-- Record only the edges not belonging to T. -/
def evenSubgraphCode (G T : SimpleGraph V) (C : EvenEdgeSubgraph G) : Set (G \ T).edgeSet :=
  {e | e.val ∈ C.val.edgeSet}

theorem graphXor_le_tree_of_code_eq (G T : SimpleGraph V)
    (A B : EvenEdgeSubgraph G) (hcode : evenSubgraphCode G T A = evenSubgraphCode G T B) :
    graphXor A.val B.val ≤ T := by
  intro x y hxy
  by_contra ht
  change (A.val.Adj x y ∧ ¬B.val.Adj x y) ∨ (B.val.Adj x y ∧ ¬A.val.Adj x y) at hxy
  have hG : G.Adj x y := hxy.elim (fun h => A.property.1 h.1) (fun h => B.property.1 h.1)
  let e : (G \ T).edgeSet := ⟨s(x, y), hG, ht⟩
  have he : A.val.Adj x y ↔ B.val.Adj x y := by
    change e ∈ evenSubgraphCode G T A ↔ e ∈ evenSubgraphCode G T B
    rw [hcode]
  exact hxy.elim (fun h => h.2 (he.mp h.1)) (fun h => h.2 (he.mpr h.1))

theorem evenSubgraphCode_injective (G T : SimpleGraph V) (hT : T.IsAcyclic) :
    Function.Injective (evenSubgraphCode G T) := by
  intro A B hcode
  have hle := graphXor_le_tree_of_code_eq G T A B hcode
  have hforest := graph_acyclic_of_le hle hT
  have heven := graphXor_even A.val B.val A.property.2 B.property.2
  have hzero := even_forest_eq_bot _ hforest heven
  apply Subtype.ext
  ext x y
  have hn : ¬(graphXor A.val B.val).Adj x y := by rw [hzero]; exact id
  simp only [graphXor, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj] at hn
  tauto

theorem off_tree_edge_count (G T : SimpleGraph V) (hG : G.Connected)
    (hTG : T ≤ G) (hT : T.IsTree) : Nat.card (G \ T).edgeSet = graphExcess G := by
  have hpart := Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hTG)
  rw [← SimpleGraph.edgeFinset_sdiff] at hpart
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hpart
  have htree := (SimpleGraph.isTree_iff_connected_and_card.mp hT).2
  have hEuler := connected_graph_excess_euler G hG
  unfold graphEdgeCount at hEuler
  omega

/-- The actual even edge-subgraphs, including the empty graph, number at
most 2^excess. The spanning tree and code injectivity are proved here. -/
theorem evenEdgeSubgraph_card_le_excess (G : SimpleGraph V) (hG : G.Connected) :
    Nat.card (EvenEdgeSubgraph G) ≤ 2 ^ graphExcess G := by
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  calc
    _ ≤ Nat.card (Set (G \ T).edgeSet) :=
      Nat.card_le_card_of_injective (evenSubgraphCode G T)
        (evenSubgraphCode_injective G T hT.IsAcyclic)
    _ = 2 ^ Nat.card (G \ T).edgeSet := by
      rw [Nat.card_eq_fintype_card, Fintype.card_set, ← Nat.card_eq_fintype_card]
    _ = _ := by rw [off_tree_edge_count G T hG hTG hT]

theorem evenEdgeSubgraph_card_le_budget (G : SimpleGraph V) (hG : G.Connected)
    (ω : ℕ) (hbudget : graphExcess G ≤ ω) :
    Nat.card (EvenEdgeSubgraph G) ≤ 2 ^ ω :=
  (evenEdgeSubgraph_card_le_excess G hG).trans (Nat.pow_le_pow_right (by decide) hbudget)

/-- Any family of distinct actual even edge patterns inherits the same bound.
This form does not choose or count cycle orientations. -/
theorem distinct_even_patterns_card_le {ι : Type*} [Fintype ι]
    (G : SimpleGraph V) (hG : G.Connected) (F : ι → SimpleGraph V)
    (hinjective : Function.Injective F) (hsub : ∀ i, F i ≤ G)
    (heven : ∀ i v, Even ((F i).degree v)) : Nat.card ι ≤ 2 ^ graphExcess G := by
  let f : ι → EvenEdgeSubgraph G := fun i => ⟨F i, hsub i, heven i⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact hinjective (congrArg Subtype.val hij)
  exact (Nat.card_le_card_of_injective f hf).trans (evenEdgeSubgraph_card_le_excess G hG)

end EvenSubgraphCode

end LocalLaw
