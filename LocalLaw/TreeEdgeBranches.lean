import LocalLaw.AdmissibleEndpointPatches

/-! # The actual two tree branches left by deleting one tree edge

Every vertex of a connected graph is reachable from one of the deleted
edge's endpoints after deletion. In a tree the endpoints are separated,
so these are exactly two disjoint genuine tree branches. Their only old
cross edge is the removed edge itself.
-/

noncomputable section
namespace LocalLaw

local instance treeEdgeBranchesDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*}

def treeEdgeDeleted (G : SimpleGraph V) (a b : V) : SimpleGraph V := G \ SimpleGraph.edge a b

def treeEdgeBranch (G : SimpleGraph V) (a b root : V) : Set V :=
  ((treeEdgeDeleted G a b).connectedComponentMk root).supp

theorem mem_treeEdgeBranch_iff (G : SimpleGraph V) (a b root v : V) :
    v ∈ treeEdgeBranch G a b root ↔ (treeEdgeDeleted G a b).Reachable root v := by
  constructor
  · exact fun h => SimpleGraph.ConnectedComponent.exact h.symm
  · exact fun h => (SimpleGraph.ConnectedComponent.sound h).symm

theorem connected_delete_edge_reachable_from_endpoints (G : SimpleGraph V) (a b : V)
    (hG : G.Connected) (v : V) :
    (treeEdgeDeleted G a b).Reachable a v ∨ (treeEdgeDeleted G a b).Reachable b v := by
  let D := treeEdgeDeleted G a b
  obtain ⟨p⟩ := hG.preconnected a v
  have haux : ∀ {u v : V} (p : G.Walk u v), u = a → D.Reachable a v ∨ D.Reachable b v := by
    intro u v p
    induction p using SimpleGraph.Walk.concatRec with
    | Hnil =>
      intro hu
      cases hu
      exact Or.inl (SimpleGraph.Reachable.refl _)
    | @Hconcat u w v p hwv ih =>
      intro hu
      by_cases he : (SimpleGraph.edge a b).Adj w v
      · rcases (SimpleGraph.edge_adj a b w v).mp he with ⟨he, _⟩
        rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (SimpleGraph.Reachable.refl _)
        · exact Or.inl (SimpleGraph.Reachable.refl _)
      · have hd : D.Adj w v := ⟨hwv, he⟩
        exact (ih hu).imp (fun h => h.trans hd.reachable) (fun h => h.trans hd.reachable)
  exact haux p rfl

theorem treeEdgeBranch_cover (G : SimpleGraph V) (a b : V) (hG : G.Connected) :
    treeEdgeBranch G a b a ∪ treeEdgeBranch G a b b = Set.univ := by
  ext v
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  exact (connected_delete_edge_reachable_from_endpoints G a b hG v).imp
    ((mem_treeEdgeBranch_iff G a b a v).mpr) ((mem_treeEdgeBranch_iff G a b b v).mpr)

theorem treeEdgeBranch_disjoint (G : SimpleGraph V) (a b : V) (hG : G.IsTree) (hab : G.Adj a b) :
    Disjoint (treeEdgeBranch G a b a) (treeEdgeBranch G a b b) := by
  have hbridge := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hG.IsAcyclic) hab
  have hNoReach : ¬(treeEdgeDeleted G a b).Reachable a b := (SimpleGraph.isBridge_iff.mp hbridge).2
  apply Set.disjoint_left.mpr
  intro v ha hb
  have hva := (mem_treeEdgeBranch_iff G a b a v).mp ha
  have hvb := (mem_treeEdgeBranch_iff G a b b v).mp hb
  exact hNoReach (hva.trans hvb.symm)

theorem treeEdgeBranch_isTree_deleted (G : SimpleGraph V) (a b root : V) (hG : G.IsTree) :
    ((treeEdgeDeleted G a b).induce (treeEdgeBranch G a b root)).IsTree := by
  let D := treeEdgeDeleted G a b
  constructor
  · exact (D.connectedComponentMk root).connected_induce_supp
  · have hD : D.IsAcyclic := graph_acyclic_of_le sdiff_le hG.IsAcyclic
    intro v p hp
    exact hD (p.map (SimpleGraph.Embedding.induce (treeEdgeBranch G a b root)).toHom)
      (hp.map Subtype.val_injective)

theorem treeEdgeBranch_old_cross_iff (G : SimpleGraph V) (a b : V) (hG : G.IsTree) (hab : G.Adj a b)
    {x y : V} (hx : x ∈ treeEdgeBranch G a b a) (hy : y ∈ treeEdgeBranch G a b b) :
    G.Adj x y ↔ (SimpleGraph.edge a b).Adj x y := by
  constructor
  · intro hxy
    by_contra hnot
    have hd : (treeEdgeDeleted G a b).Adj x y := ⟨hxy, hnot⟩
    have hyA := (mem_treeEdgeBranch_iff G a b a y).mpr
      (((mem_treeEdgeBranch_iff G a b a x).mp hx).trans hd.reachable)
    exact Set.disjoint_left.mp (treeEdgeBranch_disjoint G a b hG hab) hyA hy
  · intro he
    rcases (SimpleGraph.edge_adj a b x y).mp he with ⟨he, _⟩
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab
    · exact hab.symm

theorem treeEdgeBranch_induced_eq_deleted (G : SimpleGraph V) (a b : V) (hG : G.IsTree)
    (hab : G.Adj a b) (root : V) (hroot : root = a ∨ root = b) :
    G.induce (treeEdgeBranch G a b root) =
      (treeEdgeDeleted G a b).induce (treeEdgeBranch G a b root) := by
  ext x y
  constructor
  · intro hxy
    refine ⟨hxy, ?_⟩
    intro he
    rcases (SimpleGraph.edge_adj a b x.val y.val).mp he with ⟨he, _⟩
    have hmem {v w : V} (he : v = w) (hv : v ∈ treeEdgeBranch G a b root) :
        w ∈ treeEdgeBranch G a b root := Eq.mp (congrArg (fun z => z ∈ treeEdgeBranch G a b root) he) hv
    have hBoth : a ∈ treeEdgeBranch G a b root ∧ b ∈ treeEdgeBranch G a b root := by
      rcases he with ⟨ha, hb⟩ | ⟨hb, ha⟩
      · exact ⟨hmem ha x.property, hmem hb y.property⟩
      · exact ⟨hmem ha y.property, hmem hb x.property⟩
    rcases hroot with hroot | hroot
    · have hbA : b ∈ treeEdgeBranch G a b a := by simpa only [hroot] using hBoth.2
      exact Set.disjoint_left.mp (treeEdgeBranch_disjoint G a b hG hab) hbA
        (show b ∈ treeEdgeBranch G a b b from rfl)
    · have haB : a ∈ treeEdgeBranch G a b b := by simpa only [hroot] using hBoth.1
      exact Set.disjoint_left.mp (treeEdgeBranch_disjoint G a b hG hab)
        (show a ∈ treeEdgeBranch G a b a from rfl) haB
  · exact fun h => h.1

theorem treeEdgeBranch_isTree (G : SimpleGraph V) (a b : V) (hG : G.IsTree) (hab : G.Adj a b)
    (root : V) (hroot : root = a ∨ root = b) :
    (G.induce (treeEdgeBranch G a b root)).IsTree := by
  rw [treeEdgeBranch_induced_eq_deleted G a b hG hab root hroot]
  exact treeEdgeBranch_isTree_deleted G a b root hG

end LocalLaw
