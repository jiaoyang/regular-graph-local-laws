import LocalLaw.BallCycleWitness
import LocalLaw.CycleSpaceCounting

/-!
# A compact bicyclic witness inside a ball of excess at least two

Two distinct edges outside the actual shortest-parent spanning tree are added
to the union of their four tree root paths. That union is a tree on its own
vertex set. Adding the two genuinely new edges gives excess exactly two and
at most 4R+2 edges, with the root retained.
-/

noncomputable section
set_option maxHeartbeats 1800000

namespace LocalLaw

local instance bicyclicDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*}

/-- The edge set of a subgraph's actual vertex graph has the same edges. -/
def subgraphEdgeSetEquiv {G : SimpleGraph V} (P : G.Subgraph) : P.coe.edgeSet ≃ P.edgeSet :=
  Equiv.ofBijective
    (fun e => ⟨Sym2.map (fun v : P.verts => v.val) e.val, by
      rw [← P.image_coe_edgeSet_coe]
      exact ⟨e.val, e.property, rfl⟩⟩)
    ⟨by
      intro a b h
      apply Subtype.ext
      exact Sym2.map.injective Subtype.val_injective (congrArg Subtype.val h),
    by
      intro e
      have he : e.val ∈ Sym2.map (fun v : P.verts => v.val) '' P.coe.edgeSet := by
        rw [P.image_coe_edgeSet_coe]
        exact e.property
      obtain ⟨a, ha, heq⟩ := he
      exact ⟨⟨a, ha⟩, Subtype.ext heq⟩⟩

section Finite

variable [Fintype V]

/-- A connected actual subgraph, on its own vertices, containing the root. -/
structure RootedBicyclicSubgraph (G : SimpleGraph V) (o : V) (R : ℕ) where
  vertices : Set V
  root_mem : o ∈ vertices
  graph : SimpleGraph vertices
  le_graph : graph ≤ G.induce vertices
  connected : graph.Connected
  excess_two : graphExcess graph = 2
  edges_le : graphEdgeCount graph ≤ 4 * R + 2
  vertices_le : Nat.card vertices ≤ 4 * R + 1

theorem two_off_tree_edges (G T : SimpleGraph V) (hcard : 2 ≤ Nat.card (G \ T).edgeSet) :
    ∃ a b c d : V, G.Adj a b ∧ ¬T.Adj a b ∧ G.Adj c d ∧ ¬T.Adj c d ∧
      s(a, b) ≠ s(c, d) := by
  have hc : 1 < (Finset.univ : Finset (G \ T).edgeSet).card := by
    simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card] using hcard
  obtain ⟨e, _, f, _, hef⟩ := Finset.one_lt_card.mp hc
  rcases e with ⟨e, he⟩
  rcases f with ⟨f, hf⟩
  induction e using Sym2.ind with
  | _ a b =>
    induction f using Sym2.ind with
    | _ c d =>
      change G.Adj a b ∧ ¬T.Adj a b at he
      change G.Adj c d ∧ ¬T.Adj c d at hf
      exact ⟨a, b, c, d, he.1, he.2, hf.1, hf.2, fun h => hef (Subtype.ext h)⟩

namespace HeightParentData

variable (D : HeightParentData V)

/-- The four endpoint root paths form a tree with at most 4R edges; the two
distinct off-tree edges increase its excess to exactly two. -/
theorem bicyclic_subgraph_of_two_edges (G : SimpleGraph V) (hTG : D.tree ≤ G)
    (R : ℕ) (hheight : ∀ v, D.height v ≤ R) (a b c d : V)
    (hab : G.Adj a b) (habT : ¬D.tree.Adj a b)
    (hcd : G.Adj c d) (hcdT : ¬D.tree.Adj c d) (hne : s(a, b) ≠ s(c, d)) :
    Nonempty (RootedBicyclicSubgraph G D.root R) := by
  obtain ⟨pa, hpa⟩ := D.walk_to_root a
  obtain ⟨pb, hpb⟩ := D.walk_to_root b
  obtain ⟨pc, hpc⟩ := D.walk_to_root c
  obtain ⟨pd, hpd⟩ := D.walk_to_root d
  let P : D.tree.Subgraph := ((pa.toSubgraph ⊔ pb.toSubgraph) ⊔ pc.toSubgraph) ⊔ pd.toSubgraph
  have hAB := pa.toSubgraph_connected.sup pb.toSubgraph_connected
    ⟨D.root, pa.end_mem_verts_toSubgraph, pb.end_mem_verts_toSubgraph⟩
  have hABC := hAB.sup pc.toSubgraph_connected
    ⟨D.root, Or.inl pa.end_mem_verts_toSubgraph, pc.end_mem_verts_toSubgraph⟩
  have hP : P.Connected := hABC.sup pd.toSubgraph_connected
    ⟨D.root, Or.inl (Or.inl pa.end_mem_verts_toSubgraph), pd.end_mem_verts_toSubgraph⟩
  have hroot : D.root ∈ P.verts := Or.inl (Or.inl (Or.inl pa.end_mem_verts_toSubgraph))
  have ha : a ∈ P.verts := Or.inl (Or.inl (Or.inl pa.start_mem_verts_toSubgraph))
  have hb : b ∈ P.verts := Or.inl (Or.inl (Or.inr pb.start_mem_verts_toSubgraph))
  have hc : c ∈ P.verts := Or.inl (Or.inr pc.start_mem_verts_toSubgraph)
  have hd : d ∈ P.verts := Or.inr pd.start_mem_verts_toSubgraph
  let K := P.coe
  have hKconn : K.Connected := hP.coe
  have hKacyclic : K.IsAcyclic := by
    intro v p hp
    exact D.tree_isTree.IsAcyclic (p.map P.hom) (hp.map Subtype.val_injective)
  have hKtree : K.IsTree := ⟨hKconn, hKacyclic⟩
  have hEdgeSet : P.edgeSet.toFinset =
      ((pa.edges.toFinset ∪ pb.edges.toFinset) ∪ pc.edges.toFinset) ∪ pd.edges.toFinset := by
    ext e
    simp only [P, SimpleGraph.Subgraph.edgeSet_sup, Set.mem_toFinset, Set.mem_union,
      SimpleGraph.Walk.mem_edges_toSubgraph, Finset.mem_union, List.mem_toFinset]
  have hlenA : pa.edges.toFinset.card ≤ R := by
    exact pa.edges.toFinset_card_le.trans (by simpa only [SimpleGraph.Walk.length_edges, hpa] using hheight a)
  have hlenB : pb.edges.toFinset.card ≤ R := by
    exact pb.edges.toFinset_card_le.trans (by simpa only [SimpleGraph.Walk.length_edges, hpb] using hheight b)
  have hlenC : pc.edges.toFinset.card ≤ R := by
    exact pc.edges.toFinset_card_le.trans (by simpa only [SimpleGraph.Walk.length_edges, hpc] using hheight c)
  have hlenD : pd.edges.toFinset.card ≤ R := by
    exact pd.edges.toFinset_card_le.trans (by simpa only [SimpleGraph.Walk.length_edges, hpd] using hheight d)
  have hPcard : Nat.card P.edgeSet ≤ 4 * R := by
    have h₁ := Finset.card_union_le pa.edges.toFinset pb.edges.toFinset
    have h₂ := Finset.card_union_le (pa.edges.toFinset ∪ pb.edges.toFinset) pc.edges.toFinset
    have h₃ := Finset.card_union_le ((pa.edges.toFinset ∪ pb.edges.toFinset) ∪ pc.edges.toFinset) pd.edges.toFinset
    have hEq : Nat.card P.edgeSet = P.edgeSet.toFinset.card := by
      rw [Set.toFinset_card, Nat.card_eq_fintype_card]
    rw [hEq, hEdgeSet]
    omega
  have hKcard : graphEdgeCount K ≤ 4 * R :=
    (Nat.card_congr (subgraphEdgeSetEquiv P)).le.trans hPcard
  let aS : P.verts := ⟨a, ha⟩
  let bS : P.verts := ⟨b, hb⟩
  let cS : P.verts := ⟨c, hc⟩
  let dS : P.verts := ⟨d, hd⟩
  have habS : aS ≠ bS := fun h => hab.ne (congrArg Subtype.val h)
  have hcdS : cS ≠ dS := fun h => hcd.ne (congrArg Subtype.val h)
  have hnew₁ : ¬K.Adj aS bS := fun h => habT (P.adj_sub h)
  have hnew₂ : ¬(K ⊔ SimpleGraph.edge aS bS).Adj cS dS := by
    rintro (hK | he)
    · exact hcdT (P.adj_sub hK)
    · have hs := (SimpleGraph.adj_edge aS bS).mp he
      have heq := congrArg (Sym2.map (fun v : P.verts => v.val)) hs.1
      exact hne heq
  let W := (K ⊔ SimpleGraph.edge aS bS) ⊔ SimpleGraph.edge cS dS
  have hKW : K ≤ W := le_trans le_sup_left le_sup_left
  have hWconn : W.Connected := hKconn.mono hKW
  have hWle : W ≤ G.induce P.verts := by
    apply sup_le
    · apply sup_le
      · intro x y hxy
        exact hTG (P.adj_sub hxy)
      · exact sup_eq_left.mp ((G.induce P.verts).sup_edge_of_adj hab)
    · exact sup_eq_left.mp ((G.induce P.verts).sup_edge_of_adj hcd)
  have hWedges : graphEdgeCount W = graphEdgeCount K + 2 := by
    have h₁ := graphEdgeCount_sup_new_edge K aS bS habS hnew₁
    have h₂ := graphEdgeCount_sup_new_edge (K ⊔ SimpleGraph.edge aS bS) cS dS hcdS hnew₂
    change graphEdgeCount ((K ⊔ SimpleGraph.edge aS bS) ⊔ SimpleGraph.edge cS dS) = _
    rw [h₂, h₁]
  have hWbound : graphEdgeCount W ≤ 4 * R + 2 := by omega
  have hEuler := connected_graph_excess_euler W hWconn
  have hTreeCard := (SimpleGraph.isTree_iff_connected_and_card.mp hKtree).2
  have hExcess : graphExcess W = 2 := by
    unfold graphEdgeCount at hWedges hKcard hEuler
    omega
  have hVertices : Nat.card P.verts ≤ 4 * R + 1 := by
    unfold graphEdgeCount at hKcard
    omega
  exact ⟨⟨P.verts, hroot, W, hWle, hWconn, hExcess, hWbound, hVertices⟩⟩

theorem bicyclic_subgraph_of_excess (G : SimpleGraph V) (hTG : D.tree ≤ G)
    (R : ℕ) (hheight : ∀ v, D.height v ≤ R) (hexcess : 2 ≤ graphExcess G) :
    Nonempty (RootedBicyclicSubgraph G D.root R) := by
  have hconn : G.Connected := D.tree_connected.mono hTG
  have hoff := off_tree_edge_count G D.tree hconn hTG D.tree_isTree
  have hcard : 2 ≤ Nat.card (G \ D.tree).edgeSet := by omega
  obtain ⟨a, b, c, d, hab, habT, hcd, hcdT, hne⟩ := two_off_tree_edges G D.tree hcard
  exact D.bicyclic_subgraph_of_two_edges G hTG R hheight a b c d hab habT hcd hcdT hne

end HeightParentData

/-- Actual radius-R ball specialization, with its shortest-parent tree derived. -/
theorem ball_bicyclic_subgraph (G : SimpleGraph V) (o : V) (R : ℕ)
    (hexcess : 2 ≤ graphBallExcess G o R) :
    Nonempty (RootedBicyclicSubgraph (graphBall G o R) ⟨o, center_mem_graphBall G o R⟩ R) := by
  let D := ballHeightParentData G o R
  have hTG : D.tree ≤ graphBall G o R := D.tree_le _ (ballHeightParentData_parent_adj G o R)
  have hEx : 2 ≤ graphExcess (graphBall G o R) := by
    simpa only [graphBallExcess, graphExcess, SimpleGraph.edgeFinset_card,
      ← Nat.card_eq_fintype_card] using hexcess
  exact D.bicyclic_subgraph_of_excess _ hTG R (ballVertexHeight_le G o R) hEx

end Finite

theorem graphExcess_iso {W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) : graphExcess G = graphExcess H := by
  have he := Nat.card_congr e.mapEdgeSet
  have hv := Nat.card_congr e.toEquiv
  have hc := Nat.card_congr e.connectedComponentEquiv
  simp only [graphExcess, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  rw [he, hv, hc]

/-- A finite labelled ambient pattern for the compact bicyclic ball witness.
All its vertices lie in the original ball, and one is the original center. -/
theorem ball_bicyclic_pattern [Fintype V] (G : SimpleGraph V) (o : V) (R : ℕ)
    (hexcess : 2 ≤ graphBallExcess G o R) :
    ∃ n : ℕ, ∃ H : SimpleGraph (Fin n), ∃ f : Fin n ↪ V,
      n ≤ 4 * R + 1 ∧ H.Connected ∧ graphExcess H = 2 ∧ graphEdgeCount H ≤ 4 * R + 2 ∧
        H.map f ≤ G ∧ (∀ i, f i ∈ graphBallVertices G o R) ∧ ∃ i, f i = o := by
  obtain ⟨B⟩ := ball_bicyclic_subgraph G o R hexcess
  let S := B.vertices
  let n := Fintype.card S
  let E := Fintype.equivFin S
  let H := B.graph.map E.toEmbedding
  let J : S ↪ V :=
    { toFun := fun v => v.val.val
      inj' := by
        intro x y h
        apply Subtype.ext
        exact Subtype.ext h }
  let f : Fin n ↪ V := E.symm.toEmbedding.trans J
  have he : B.graph ≃g H := SimpleGraph.Iso.map E B.graph
  have hn : n ≤ 4 * R + 1 := by
    simpa only [n, S, Nat.card_eq_fintype_card] using B.vertices_le
  have hconn : H.Connected := he.connected_iff.mp B.connected
  have hEx : graphExcess H = 2 := (graphExcess_iso he).symm.trans B.excess_two
  have hEdges : graphEdgeCount H ≤ 4 * R + 2 :=
    (mappedPattern_edgeCount B.graph E.toEmbedding).le.trans B.edges_le
  have hsub : H.map f ≤ G := by
    apply (mappedPattern_le_iff _ _ _).mpr
    intro i j hij
    obtain ⟨x, y, hxy, hx, hy⟩ := (SimpleGraph.map_adj E.toEmbedding B.graph i j).mp hij
    have hi : E.symm i = x := by rw [← hx]; exact E.symm_apply_apply x
    have hj : E.symm j = y := by rw [← hy]; exact E.symm_apply_apply y
    change G.Adj (J (E.symm i)) (J (E.symm j))
    rw [hi, hj]
    exact B.le_graph hxy
  have hBall : ∀ i, f i ∈ graphBallVertices G o R := by
    intro i
    exact (E.symm i).val.property
  have hRoot : ∃ i, f i = o := by
    let rootS : S := ⟨⟨o, center_mem_graphBall G o R⟩, B.root_mem⟩
    refine ⟨E rootS, ?_⟩
    change J (E.symm (E rootS)) = o
    rw [E.symm_apply_apply]
    rfl
  exact ⟨n, H, f, hn, hconn, hEx, hEdges, hsub, hBall, hRoot⟩

end LocalLaw
