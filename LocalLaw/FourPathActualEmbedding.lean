import LocalLaw.TreePathGraft
import LocalLaw.PathGraftGraph
import LocalLaw.BicyclicFourPathEncoding

/-!
# Encoding actual root paths by canonical finite path grafts

A connected finite graph already injected into a tree has a connected induced
image. Each further simple root path therefore extends that injection by one
fresh path tail, retaining every old label and tracking the new endpoint.
-/

namespace LocalLaw
noncomputable section
local instance actualGraftDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} {T : SimpleGraph V}

/-- An edge-preserving finite injection from a connected graph has connected
induced image in the ambient graph. -/
theorem connected_embedding_range {n : ℕ} (G : SimpleGraph (Fin n))
    (e : Fin n ↪ V) (hG : G.Connected)
    (he : ∀ i j, G.Adj i j → T.Adj (e i) (e j)) :
    (T.induce (Set.range e)).Connected := by
  let f : G →g T.induce (Set.range e) :=
    { toFun := fun i => ⟨e i, ⟨i, rfl⟩⟩
      map_rel' := fun h => he _ _ h }
  have hf : Function.Surjective f := by
    rintro ⟨v, i, hi⟩
    exact ⟨i, Subtype.ext hi⟩
  exact hG.map f hf

/-- One actual simple root path is encoded by a single canonical graft.
Neither a fresh tail nor an embedding extension is assumed. -/
theorem actual_root_path_graft [DecidableEq V] {n R : ℕ}
    (hT : T.IsAcyclic) (G : SimpleGraph (Fin n)) (hG : G.Connected)
    (e : Fin n ↪ V) (he : ∀ i j, G.Adj i j → T.Adj (e i) (e j))
    (root v : V) (hroot : root ∈ Set.range e)
    (p : T.Walk root v) (hp : p.IsPath) (hR : p.length ≤ R) :
    ∃ ell : ℕ, ell ≤ R ∧ ∃ g : Fin n, ∃ e' : Fin (n + ell) ↪ V,
      (∀ i j, (pathGraftGraph G g ell).Adj i j → T.Adj (e' i) (e' j)) ∧
      (∀ i, e' (Fin.castAdd ell i) = e i) ∧
      e' (pathGraftEndpoint g ell) = v := by
  have hS := connected_embedding_range G e hG he
  obtain ⟨w, hw, hwS, _hprefix, hfresh, htail, hlen⟩ :=
    tree_path_graft_tail hT (Set.range e) hS root v hroot p hp
  obtain ⟨g, hg⟩ := hwS
  subst w
  let q := p.dropUntil (e g) hw
  have hq : q.IsPath := htail
  have hqfresh : ∀ k : Fin q.length, q.getVert (k.val + 1) ∉ Set.range e := by
    intro k
    apply hfresh _ (q.getVert_mem_support _) ?_
    intro h
    have hi : k.val + 1 ≤ q.length := by have hk := k.is_lt; omega
    have heq : q.getVert (k.val + 1) = q.getVert 0 := by rw [q.getVert_zero]; exact h
    have hzero := hq.getVert_injOn hi (Nat.zero_le _) heq
    omega
  let e' := pathGraftEmbedding g e q hq rfl hqfresh
  refine ⟨q.length, hlen.trans hR, g, e', ?_, ?_, ?_⟩
  · exact pathGraftEmbedding_adj G g e q hq rfl hqfresh he
  · exact pathGraftEmbedding_old g e q hq rfl hqfresh
  · exact pathGraftEmbedding_endpoint g e q hq rfl hqfresh

/-- Four arbitrary bounded simple root paths admit the exact canonical
four-tail parameter encoding, with all four physical endpoints retained. -/
theorem actual_four_root_paths [DecidableEq V] {R : ℕ}
    (hT : T.IsTree) (root : V) (v : Fin 4 → V)
    (p : ∀ i, T.Walk root (v i)) (hp : ∀ i, (p i).IsPath)
    (hR : ∀ i, (p i).length ≤ R) :
    ∃ P : FourPathParameters R, ∃ e : Fin (fourStageSize P.1 4) ↪ V,
      (∀ i j, (fourTrieGraph P 4 le_rfl).Adj i j → T.Adj (e i) (e j)) ∧
      (∀ i, e (fourMarkedTarget P i) = v i) := by
  let G0 : SimpleGraph (Fin 1) := ⊥
  let e0 : Fin 1 ↪ V :=
    { toFun := fun _ => root
      inj' := fun _ _ _ => Subsingleton.elim _ _ }
  have hG0 : G0.Connected := by
    apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
    refine ⟨0, ?_⟩
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact SimpleGraph.Reachable.rfl
  have he0 : ∀ i j, G0.Adj i j → T.Adj (e0 i) (e0 j) := by simp [G0]
  have hr0 : root ∈ Set.range e0 := ⟨0, rfl⟩
  obtain ⟨ell0, h0, g0, e1, he1, hold1, hend1⟩ :=
    actual_root_path_graft hT.IsAcyclic G0 hG0 e0 he0 root (v 0) hr0 (p 0) (hp 0) (hR 0)
  have hg0 : g0 = 0 := Subsingleton.elim _ _
  subst g0
  let G1 := pathGraftGraph G0 0 ell0
  have hG1 : G1.Connected := pathGraftGraph_connected G0 0 ell0 hG0
  have hr1 : root ∈ Set.range e1 := ⟨Fin.castAdd ell0 0, hold1 0⟩
  obtain ⟨ell1, h1, g1, e2, he2, hold2, hend2⟩ :=
    actual_root_path_graft hT.IsAcyclic G1 hG1 e1 he1 root (v 1) hr1 (p 1) (hp 1) (hR 1)
  let G2 := pathGraftGraph G1 g1 ell1
  have hG2 : G2.Connected := pathGraftGraph_connected G1 g1 ell1 hG1
  have hr2 : root ∈ Set.range e2 := by
    obtain ⟨j, hj⟩ := hr1
    exact ⟨Fin.castAdd ell1 j, (hold2 j).trans hj⟩
  obtain ⟨ell2, h2, g2, e3, he3, hold3, hend3⟩ :=
    actual_root_path_graft hT.IsAcyclic G2 hG2 e2 he2 root (v 2) hr2 (p 2) (hp 2) (hR 2)
  let G3 := pathGraftGraph G2 g2 ell2
  have hG3 : G3.Connected := pathGraftGraph_connected G2 g2 ell2 hG2
  have hr3 : root ∈ Set.range e3 := by
    obtain ⟨j, hj⟩ := hr2
    exact ⟨Fin.castAdd ell2 j, (hold3 j).trans hj⟩
  obtain ⟨ell3, h3, g3, e4, he4, hold4, hend4⟩ :=
    actual_root_path_graft hT.IsAcyclic G3 hG3 e3 he3 root (v 3) hr3 (p 3) (hp 3) (hR 3)
  let l0 : Fin (R + 1) := ⟨ell0, by omega⟩
  let l1 : Fin (R + 1) := ⟨ell1, by omega⟩
  let l2 : Fin (R + 1) := ⟨ell2, by omega⟩
  let l3 : Fin (R + 1) := ⟨ell3, by omega⟩
  let P := fourPathParametersMk l0 l1 l2 l3 g1 g2 g3
  refine ⟨P, e4, ?_, ?_⟩
  · change ∀ i j, (pathGraftGraph G3 g3 ell3).Adj i j → T.Adj (e4 i) (e4 j)
    exact he4
  · intro i
    fin_cases i
    · change e4 (Fin.castAdd ell3 (Fin.castAdd ell2 (Fin.castAdd ell1
        (pathGraftEndpoint (0 : Fin 1) ell0)))) = v 0
      rw [hold4, hold3, hold2, hend1]
    · change e4 (Fin.castAdd ell3 (Fin.castAdd ell2 (pathGraftEndpoint g1 ell1))) = v 1
      rw [hold4, hold3, hend2]
    · change e4 (Fin.castAdd ell3 (pathGraftEndpoint g2 ell2)) = v 2
      rw [hold4, hend3]
    · change e4 (pathGraftEndpoint g3 ell3) = v 3
      exact hend4

namespace HeightParentData

/-- Two distinct edges outside a bounded-height parent tree yield an actual
occurrence in the polynomial canonical four-tail family. -/
theorem four_path_pattern_of_two_edges [Fintype V] [DecidableEq V]
    (D : HeightParentData V) (G : SimpleGraph V) (hTG : D.tree ≤ G)
    (R : ℕ) (hheight : ∀ v, D.height v ≤ R) (a b c d : V)
    (hab : G.Adj a b) (habT : ¬D.tree.Adj a b)
    (hcd : G.Adj c d) (hcdT : ¬D.tree.Adj c d) (hne : s(a, b) ≠ s(c, d)) :
    ∃ P : FourPathParameters R, graphExcess (fourPathBicyclicGraph P) = 2 ∧
      ∃ e : Fin (fourStageSize P.1 4) ↪ V, (fourPathBicyclicGraph P).map e ≤ G := by
  let v : Fin 4 → V := ![a, b, c, d]
  choose p hp using fun i : Fin 4 => D.walk_to_root (v i)
  let q (i : Fin 4) := (p i).reverse.bypass
  have hq : ∀ i, (q i).IsPath := fun i => (p i).reverse.bypass_isPath
  have hqlen : ∀ i, (q i).length ≤ R := by
    intro i
    exact ((p i).reverse.length_bypass_le).trans
      (by simpa only [SimpleGraph.Walk.length_reverse, hp] using hheight (v i))
  obtain ⟨P, e, he, hmark⟩ := actual_four_root_paths D.tree_isTree D.root v q hq hqlen
  let K := fourTrieGraph P 4 le_rfl
  let A := fourMarkedTarget P 0
  let B := fourMarkedTarget P 1
  let C := fourMarkedTarget P 2
  let E := fourMarkedTarget P 3
  have hA : e A = a := hmark 0
  have hB : e B = b := hmark 1
  have hC : e C = c := hmark 2
  have hE : e E = d := hmark 3
  have hAB : A ≠ B := by intro h; exact hab.ne (by rw [← hA, ← hB, h])
  have hCE : C ≠ E := by intro h; exact hcd.ne (by rw [← hC, ← hE, h])
  have hnew₁ : ¬K.Adj A B := by
    intro h
    have hh := he A B h
    rw [hA, hB] at hh
    exact habT hh
  have hnew₂ : ¬(K ⊔ SimpleGraph.edge A B).Adj C E := by
    rintro (h | h)
    · have hh := he C E h
      rw [hC, hE] at hh
      exact hcdT hh
    · have hh := (SimpleGraph.adj_edge A B).mp h
      have heq := congrArg (Sym2.map e) hh.1
      have hbad : s(a, b) = s(c, d) := by
        simpa only [Sym2.map_pair_eq, hA, hB, hC, hE] using heq
      exact hne hbad
  have hedges : graphEdgeCount (fourPathBicyclicGraph P) = graphEdgeCount K + 2 := by
    change graphEdgeCount ((K ⊔ SimpleGraph.edge A B) ⊔ SimpleGraph.edge C E) = _
    rw [graphEdgeCount_sup_new_edge _ C E hCE hnew₂,
      graphEdgeCount_sup_new_edge _ A B hAB hnew₁]
  have htree := (SimpleGraph.isTree_iff_connected_and_card.mp (fourTrieGraph_isTree P 4 le_rfl)).2
  have heuler := connected_graph_excess_euler (fourPathBicyclicGraph P)
    (fourPathBicyclicGraph_connected P)
  have hexcess : graphExcess (fourPathBicyclicGraph P) = 2 := by
    change graphEdgeCount K + 1 = Nat.card (Fin (fourStageSize P.1 4)) at htree
    omega
  refine ⟨P, hexcess, e, ?_⟩
  apply (mappedPattern_le_iff _ _ _).mpr
  have hK : K ≤ G.comap e := fun i j hij => hTG (he i j hij)
  have hABG : (G.comap e).Adj A B := by change G.Adj (e A) (e B); rw [hA, hB]; exact hab
  have hCEG : (G.comap e).Adj C E := by change G.Adj (e C) (e E); rw [hC, hE]; exact hcd
  have hsub : fourPathBicyclicGraph P ≤ G.comap e := by
    exact sup_le (sup_le hK (sup_eq_left.mp ((G.comap e).sup_edge_of_adj hABG)))
      (sup_eq_left.mp ((G.comap e).sup_edge_of_adj hCEG))
  exact hsub

/-- The canonical pattern is obtained from every excess-at-least-two graph
with a bounded-height spanning parent tree. -/
theorem four_path_pattern_of_excess [Fintype V] [DecidableEq V]
    (D : HeightParentData V) (G : SimpleGraph V) (hTG : D.tree ≤ G)
    (R : ℕ) (hheight : ∀ v, D.height v ≤ R) (hexcess : 2 ≤ graphExcess G) :
    ∃ P : FourPathParameters R, graphExcess (fourPathBicyclicGraph P) = 2 ∧
      ∃ e : Fin (fourStageSize P.1 4) ↪ V, (fourPathBicyclicGraph P).map e ≤ G := by
  have hconn : G.Connected := D.tree_connected.mono hTG
  have hoff := off_tree_edge_count G D.tree hconn hTG D.tree_isTree
  have hcard : 2 ≤ Nat.card (G \ D.tree).edgeSet := by omega
  obtain ⟨a, b, c, d, hab, habT, hcd, hcdT, hne⟩ := two_off_tree_edges G D.tree hcard
  exact D.four_path_pattern_of_two_edges G hTG R hheight a b c d hab habT hcd hcdT hne

end HeightParentData

/-- Every actual bad radius-R ball contains a valid member of the polynomial
four-tail family, injected into the original ambient graph. -/
theorem ball_four_path_bicyclic_pattern [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (o : V) (R : ℕ) (hexcess : 2 ≤ graphBallExcess G o R) :
    ∃ P : FourPathParameters R, graphExcess (fourPathBicyclicGraph P) = 2 ∧
      ∃ e : Fin (fourStageSize P.1 4) ↪ V, (fourPathBicyclicGraph P).map e ≤ G := by
  let D := ballHeightParentData G o R
  have hTG : D.tree ≤ graphBall G o R := D.tree_le _ (ballHeightParentData_parent_adj G o R)
  have hEx : 2 ≤ graphExcess (graphBall G o R) := by
    simpa only [graphBallExcess, graphExcess, SimpleGraph.edgeFinset_card,
      ← Nat.card_eq_fintype_card] using hexcess
  obtain ⟨P, hP, e, he⟩ := D.four_path_pattern_of_excess _ hTG R (ballVertexHeight_le G o R) hEx
  let j : graphBallVertices G o R ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨P, hP, e.trans j, ?_⟩
  apply (mappedPattern_le_iff _ _ _).mpr
  intro a b hab
  have hball := (mappedPattern_le_iff _ _ _).mp he a b hab
  exact hball

end
end LocalLaw
