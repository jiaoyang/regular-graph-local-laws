import LocalLaw.TreeGluing
import LocalLaw.GraphModel

/-!
# Separated induced trees joined by one actual new edge

For disjoint vertex sets with no original cross edge, the augmented induced
union is isomorphic to the explicit one-edge join of the two induced trees.
This supplies the exact finite I-test construction.
-/

noncomputable section
namespace LocalLaw

local instance separatedTreeGluingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V]

theorem induce_union_add_bridge_isTree (G : SimpleGraph V) (A B : Set V)
    (hdis : Disjoint A B) (hcross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y)
    (a b : V) (ha : a ∈ A) (hb : b ∈ B)
    (hA : (G.induce A).IsTree) (hB : (G.induce B).IsTree) :
    ((G ⊔ SimpleGraph.edge a b).induce (A ∪ B)).IsTree := by
  have haNotB : a ∉ B := fun h => Set.disjoint_left.mp hdis ha h
  have hbNotA : b ∉ A := fun h => Set.disjoint_left.mp hdis h hb
  let e : treeJoin (G.induce A) (G.induce B) (⟨a, ha⟩ : A) (⟨b, hb⟩ : B) ≃g
      ((G ⊔ SimpleGraph.edge a b).induce (A ∪ B)) :=
    { toEquiv := (Equiv.Set.union hdis).symm
      map_rel_iff' := by
        rintro (x | x) (y | y)
        · change (G.Adj x.val y.val ∨ (SimpleGraph.edge a b).Adj x.val y.val) ↔
            (treeJoin (G.induce A) (G.induce B) ⟨a, ha⟩ ⟨b, hb⟩).Adj (Sum.inl x) (Sum.inl y)
          simp only [treeJoin, SimpleGraph.sup_adj, SimpleGraph.sum, SimpleGraph.edge_adj,
            Sum.inl.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, false_and, and_false,
            false_or, or_false, Subtype.ext_iff]
          have hx := x.property
          have hy := y.property
          aesop
        · change (G.Adj x.val y.val ∨ (SimpleGraph.edge a b).Adj x.val y.val) ↔
            (treeJoin (G.induce A) (G.induce B) ⟨a, ha⟩ ⟨b, hb⟩).Adj (Sum.inl x) (Sum.inr y)
          have hxy : x.val ≠ y.val := fun h => Set.disjoint_left.mp hdis x.property (h ▸ y.property)
          have hno := hcross x.val x.property y.val y.property
          simp only [treeJoin, SimpleGraph.sup_adj, SimpleGraph.sum, SimpleGraph.edge_adj,
            Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
            false_and, and_false, false_or, or_false, Subtype.ext_iff, hno, hxy,
            not_false_eq_true, and_true]
          have hx := x.property
          have hy := y.property
          aesop
        · change (G.Adj x.val y.val ∨ (SimpleGraph.edge a b).Adj x.val y.val) ↔
            (treeJoin (G.induce A) (G.induce B) ⟨a, ha⟩ ⟨b, hb⟩).Adj (Sum.inr x) (Sum.inl y)
          have hxy : x.val ≠ y.val := fun h => Set.disjoint_left.mp hdis (h ▸ y.property) x.property
          have hno : ¬ G.Adj x.val y.val := fun h => hcross y.val y.property x.val x.property h.symm
          simp only [treeJoin, SimpleGraph.sup_adj, SimpleGraph.sum, SimpleGraph.edge_adj,
            Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
            false_and, and_false, false_or, or_false, Subtype.ext_iff, hno, hxy,
            not_false_eq_true, and_true]
          have hx := x.property
          have hy := y.property
          aesop
        · change (G.Adj x.val y.val ∨ (SimpleGraph.edge a b).Adj x.val y.val) ↔
            (treeJoin (G.induce A) (G.induce B) ⟨a, ha⟩ ⟨b, hb⟩).Adj (Sum.inr x) (Sum.inr y)
          simp only [treeJoin, SimpleGraph.sup_adj, SimpleGraph.sum, SimpleGraph.edge_adj,
            Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, false_and, and_false,
            false_or, or_false, Subtype.ext_iff]
          have hx := x.property
          have hy := y.property
          aesop }
  have ht := treeJoin_isTree (G.induce A) (G.induce B) ⟨a, ha⟩ ⟨b, hb⟩ hA hB
  refine ⟨e.connected_iff.mp ht.isConnected, ?_⟩
  intro v p hp
  exact ht.IsAcyclic (p.map e.symm.toHom) (hp.map e.symm.injective)

end LocalLaw
