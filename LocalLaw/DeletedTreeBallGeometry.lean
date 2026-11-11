import LocalLaw.VertexDeletionModel
import LocalLaw.TreeReferenceKernel
import LocalLaw.ComponentBallGeometry

/-!
# Actual tree geometry after deleting one endpoint

In an acyclic common ball, two distinct neighbors of the deleted endpoint
cannot be joined while avoiding that endpoint. This supplies the one-root
deficit of the actual cavity ball, rather than assuming a canonical tree.
-/

noncomputable section
namespace LocalLaw
local instance deletedTreeBallDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) deletedTreeBallSingletonMemDecidable {A : Type*} (b : A) :
    DecidablePred (fun a => a ∈ ({b} : Set A)) := fun _ => Classical.propDecidable _

variable {V : Type*} {G : SimpleGraph V}

theorem acyclic_adjacent_endpoints_of_avoiding_path (hG : G.IsAcyclic)
    {b c v : V} (hbc : G.Adj b c) (hbv : G.Adj b v)
    (p : G.Walk c v) (hp : p.IsPath) (hb : b ∉ p.support) : v = c := by
  have heq : p.cons hbc = SimpleGraph.Walk.cons hbv SimpleGraph.Walk.nil :=
    congrArg Subtype.val (hG.path_unique ⟨_, hp.cons hb⟩ (SimpleGraph.Path.singleton hbv))
  have hh := congrArg (fun w : G.Walk b v => w.getVert 1) heq
  simpa only [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_zero] using hh.symm

def deletedBallAmbientHom (G : SimpleGraph V) (b : V) (c : {v : V // v ≠ b}) (r : ℕ) :
    graphBall (G.induce {v | v ≠ b}) c r →g graphBall G c.val (r + 1) where
  toFun v := ⟨v.val.val, by
    have hh := (graphHom_edist_le
      (SimpleGraph.Embedding.induce (G := G) {v | v ≠ b}).toHom c v.val).trans v.property
    exact hh.trans (by exact_mod_cast Nat.le_succ r)⟩
  map_rel' := fun h => h

theorem deletedBallAmbientHom_injective (G : SimpleGraph V) (b : V)
    (c : {v : V // v ≠ b}) (r : ℕ) : Function.Injective (deletedBallAmbientHom G b c r) := by
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun v : graphBallVertices G c.val (r + 1) => v.val) h))

theorem deleted_ball_isTree (G : SimpleGraph V) (b : V) (c : {v : V // v ≠ b}) (r : ℕ)
    (hTree : (graphBall G c.val (r + 1)).IsTree) :
    (graphBall (G.induce {v | v ≠ b}) c r).IsTree := by
  refine ⟨graphBall_connected _ _ _, ?_⟩
  intro v p hp
  exact hTree.IsAcyclic (p.map (deletedBallAmbientHom G b c r))
    (hp.map (deletedBallAmbientHom_injective G b c r))

theorem neighbor_in_deleted_tree_ball (G : SimpleGraph V) (b : V)
    (c : {v : V // v ≠ b}) (hbc : G.Adj b c.val) (r : ℕ)
    (hTree : (graphBall G c.val (r + 1)).IsTree)
    (v : graphBallVertices (G.induce {v | v ≠ b}) c r) (hbv : G.Adj b v.val.val) :
    v.val = c := by
  let H := graphBall G c.val (r + 1)
  let K := graphBall (G.induce {v | v ≠ b}) c r
  let f := deletedBallAmbientHom G b c r
  let cc : graphBallVertices (G.induce {v | v ≠ b}) c r := ⟨c, center_mem_graphBall _ _ _⟩
  let bb : graphBallVertices G c.val (r + 1) := ⟨b, by
    change G.edist c.val b ≤ ((r + 1 : ℕ) : ℕ∞)
    rw [SimpleGraph.edist_eq_one_iff_adj.mpr hbc.symm]
    exact_mod_cast (show 1 ≤ r + 1 by omega)⟩
  obtain ⟨p, hp, _⟩ := (graphBall_connected (G.induce {v | v ≠ b}) c r).preconnected cc v |>.exists_path_of_dist
  have hbavoid : bb ∉ (p.map f).support := by
    intro hh
    rw [SimpleGraph.Walk.support_map] at hh
    obtain ⟨w, _, hw⟩ := List.mem_map.mp hh
    have hwval : w.val.val = b := congrArg Subtype.val hw
    exact w.val.property hwval
  have heq := acyclic_adjacent_endpoints_of_avoiding_path hTree.IsAcyclic
    (show H.Adj bb (f cc) from hbc) (show H.Adj bb (f v) from hbv)
    (p.map f) (SimpleGraph.Walk.map_isPath_of_injective (deletedBallAmbientHom_injective G b c r) hp) hbavoid
  exact Subtype.ext (congrArg (fun x : graphBallVertices G c.val (r + 1) => x.val) heq)

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

omit [DecidableEq V] in
theorem delete_degree_deficit_sum (g : DeficientGraph V d) (T : Set V) (v : (Tᶜ : Set V)) :
    (g.delete T).graph.degree v + (g.delete T).deficit v = g.graph.degree v.val + g.deficit v.val := by
  have hh := induced_degree_le g.graph Tᶜ v
  rw [g.delete_deficit]
  change (g.graph.induce Tᶜ).degree v + (g.deficit v.val +
    (g.graph.degree v.val - (g.graph.induce Tᶜ).degree v)) = _
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh ⊢
  omega

theorem deleteVertex_degree_deficit_sum (g : DeficientGraph V d) (b : V) (v : {v : V // v ≠ b}) :
    (g.deleteVertex b).graph.degree v + (g.deleteVertex b).deficit v =
      g.graph.degree v.val + g.deficit v.val := by
  have hh := induced_degree_le g.graph {v | v ≠ b} v
  change (g.graph.induce {v | v ≠ b}).degree v + (g.deficit v.val +
    (g.graph.degree v.val - (g.graph.induce {v | v ≠ b}).degree v)) = _
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh ⊢
  omega

theorem deleteVertex_deficit_eq_adj (g : DeficientGraph V d) (b : V) (v : {v : V // v ≠ b}) :
    (g.deleteVertex b).deficit v = g.deficit v.val + if g.graph.Adj b v.val then 1 else 0 := by
  rw [g.deleteVertex_deficit_iso, g.delete_deficit_eq_removed_neighbors]
  change g.deficit v.val + Nat.card {t : ({b} : Set V) // g.graph.Adj t.val v.val} = _
  congr 1
  by_cases hadj : g.graph.Adj b v.val
  · letI : Unique {t : ({b} : Set V) // g.graph.Adj t.val v.val} :=
      ⟨⟨⟨b, rfl⟩, hadj⟩, fun t => Subtype.ext (Subtype.ext t.val.property)⟩
    simp only [if_pos hadj, Nat.card_unique]
  · letI : IsEmpty {t : ({b} : Set V) // g.graph.Adj t.val v.val} := ⟨fun t => by
      have ht : t.val.val = b := t.val.property
      have hh := t.property
      rw [ht] at hh
      exact hadj hh⟩
    simp only [if_neg hadj, Nat.card_of_isEmpty]

/-- A genuine acyclic common ball makes the actual deleted deficit equal
to one at its cavity root and zero everywhere else in that cavity ball. -/
theorem deleted_tree_ball_one_root_deficit (g : DeficientGraph V d) (b : V)
    (c : {v : V // v ≠ b}) (hbc : g.graph.Adj b c.val) (r : ℕ)
    (hTree : (graphBall g.graph c.val (r + 1)).IsTree)
    (hzero : ∀ v ∈ graphBallVertices g.graph c.val (r + 1), g.deficit v = 0)
    (v : graphBallVertices (g.deleteVertex b).graph c r) :
    (g.deleteVertex b).deficit v.val = if v.val = c then 1 else 0 := by
  have hvzero := hzero v.val.val (deletedBallAmbientHom g.graph b c r v).property
  rw [g.deleteVertex_deficit_eq_adj, hvzero, zero_add]
  congr 1
  apply propext
  constructor
  · exact neighbor_in_deleted_tree_ball g.graph b c hbc r hTree v
  · intro hh
    simpa only [hh] using hbc

end DeficientGraph
end LocalLaw
