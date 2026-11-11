import LocalLaw.ExcessCutset

/-!
# Joining two actual finite trees by one edge

The tree assertion follows from an actual dart partition, exact edge count,
and connectivity. It will be used for the resampling I-test: the separated
boundary-root tree and sampled-edge tree become one tree after inserting
the single edge between them.
-/

noncomputable section
namespace LocalLaw

local instance treeGluingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {U V : Type*}

def sumGraphDartEquiv (G : SimpleGraph U) (H : SimpleGraph V) :
    (G ⊕g H).Dart ≃ G.Dart ⊕ H.Dart where
  toFun := by
    rintro ⟨⟨x, y⟩, h⟩
    cases x with
    | inl x =>
      cases y with
      | inl y => exact Sum.inl ⟨(x, y), h⟩
      | inr y => simp [SimpleGraph.sum] at h
    | inr x =>
      cases y with
      | inl y => simp [SimpleGraph.sum] at h
      | inr y => exact Sum.inr ⟨(x, y), h⟩
  invFun := fun e => match e with
    | Sum.inl e => ⟨(Sum.inl e.fst, Sum.inl e.snd), e.adj⟩
    | Sum.inr e => ⟨(Sum.inr e.fst, Sum.inr e.snd), e.adj⟩
  left_inv := by
    rintro ⟨⟨x, y⟩, h⟩
    cases x <;> cases y
    · rfl
    · simp [SimpleGraph.sum] at h
    · simp [SimpleGraph.sum] at h
    · rfl
  right_inv := by rintro (e | e) <;> rfl

variable [Fintype U] [Fintype V]

theorem graphEdgeCount_sum (G : SimpleGraph U) (H : SimpleGraph V) :
    graphEdgeCount (G ⊕g H) = graphEdgeCount G + graphEdgeCount H := by
  have h := Nat.card_congr (sumGraphDartEquiv G H)
  rw [Nat.card_sum, graph_dart_count, graph_dart_count, graph_dart_count] at h
  omega

def treeJoin (G : SimpleGraph U) (H : SimpleGraph V) (a : U) (b : V) : SimpleGraph (U ⊕ V) :=
  (G ⊕g H) ⊔ SimpleGraph.edge (Sum.inl a) (Sum.inr b)

omit [Fintype U] [Fintype V] in
theorem treeJoin_connected (G : SimpleGraph U) (H : SimpleGraph V) (a : U) (b : V)
    (hG : G.Connected) (hH : H.Connected) : (treeJoin G H a b).Connected := by
  let fG : G →g treeJoin G H a b :=
    { toFun := Sum.inl
      map_rel' := fun h => Or.inl h }
  let fH : H →g treeJoin G H a b :=
    { toFun := Sum.inr
      map_rel' := fun h => Or.inl h }
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨Sum.inl a, ?_⟩
  intro x
  cases x with
  | inl x => exact (hG a x).map fG
  | inr x =>
    have hedge : (treeJoin G H a b).Adj (Sum.inl a) (Sum.inr b) :=
      Or.inr ((SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, Sum.inl_ne_inr⟩)
    exact hedge.reachable.trans ((hH b x).map fH)

theorem treeJoin_edgeCount (G : SimpleGraph U) (H : SimpleGraph V) (a : U) (b : V) :
    graphEdgeCount (treeJoin G H a b) = graphEdgeCount G + graphEdgeCount H + 1 := by
  have hnot : ¬ (G ⊕g H).Adj (Sum.inl a) (Sum.inr b) := by simp [SimpleGraph.sum]
  have h := (G ⊕g H).card_edgeFinset_sup_edge hnot (Sum.inl_ne_inr (a := a) (b := b))
  have hsum := graphEdgeCount_sum G H
  simp only [treeJoin, graphEdgeCount, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card] at h hsum ⊢
  omega

theorem treeJoin_isTree (G : SimpleGraph U) (H : SimpleGraph V) (a : U) (b : V)
    (hG : G.IsTree) (hH : H.IsTree) : (treeJoin G H a b).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨treeJoin_connected G H a b hG.isConnected hH.isConnected, ?_⟩
  have hE := treeJoin_edgeCount G H a b
  have h₁ := (SimpleGraph.isTree_iff_connected_and_card.mp hG).2
  have h₂ := (SimpleGraph.isTree_iff_connected_and_card.mp hH).2
  simp only [graphEdgeCount, Nat.card_sum] at hE ⊢
  omega

end LocalLaw
