import LocalLaw.ZeroDeficitForestReference

/-! # Tree values inside arbitrary induced restrictions

The restriction need not contain an ambient ball. Its own pair neighborhood
embeds into the ambient tree patch, and missing degrees carry the physical
boundary value. The resulting diagonal and adjacent values are exact.
-/

noncomputable section
namespace LocalLaw
local instance restrictedTreePatchDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

def inducedPairBallAmbientMap (G : SimpleGraph V) (S : Set V) (u v : S) (r k : ℕ)
    (hcenters : G.edist u.val v.val≤(k:ℕ∞)) :
    pairBallGraph (G.induce S) u v r →g graphBall G u.val (r+k) where
  toFun x := ⟨x.val.val,by
    have hmap (a b : S) : G.edist a.val b.val≤(G.induce S).edist a b :=
      graphHom_edist_le (SimpleGraph.Embedding.induce (G:=G) S).toHom a b
    rcases x.property with hu|hv
    · exact ((hmap u x.val).trans hu).trans (ENat.coe_le_coe.mpr (show r≤r+k by omega))
    · calc
        _ ≤ G.edist u.val v.val+G.edist v.val x.val.val := G.edist_triangle
        _ ≤ (k:ℕ∞)+(r:ℕ∞) := add_le_add hcenters ((hmap v x.val).trans hv)
        _ = _ := by exact_mod_cast (Nat.add_comm k r)⟩
  map_rel' := fun h => h

theorem inducedPairBallAmbientMap_injective (G : SimpleGraph V) (S : Set V) (u v : S) (r k : ℕ)
    (hcenters : G.edist u.val v.val≤(k:ℕ∞)) :
    Function.Injective (inducedPairBallAmbientMap G S u v r k hcenters) := by
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun a : graphBallVertices G u.val (r+k) => a.val) h))

theorem induced_pairBall_acyclic_of_ambient_tree (G : SimpleGraph V) (S : Set V) (u v : S) (r k : ℕ)
    (hcenters : G.edist u.val v.val≤(k:ℕ∞)) (htree : (graphBall G u.val (r+k)).IsTree) :
    (pairBallGraph (G.induce S) u v r).IsAcyclic := by
  let f := inducedPairBallAmbientMap G S u v r k hcenters
  have hinj := inducedPairBallAmbientMap_injective G S u v r k hcenters
  intro x p hp
  exact htree.IsAcyclic (p.map f) (hp.map hinj)

namespace DeficientGraph
variable [Fintype V] [DecidableEq V] {d : ℕ}

theorem restrict_P_diagonal_of_ambient_tree (g : DeficientGraph V d) (hd : 3≤d)
    (S : Set V) (root : S) (r : ℕ)
    (htree : (graphBall g.graph root.val r).IsTree)
    (hzero : ∀ v∈graphBallVertices g.graph root.val r,g.deficit v=0)
    (m z : ℂ) (hm : m^2+z*m+1=0) (hz : 0<z.im) (hmim : 0 ≤ m.im) :
    (g.restrict S).P r z m root root=kestenMcKayTransform d m z := by
  let M := g.restrict S
  let A := pairBallVertices M.graph root root r
  let K := M.restrict A
  let f := inducedPairBallAmbientMap g.graph S root root r 0 (by simp)
  have htree' : (graphBall g.graph root.val (r+0)).IsTree := by simpa only [Nat.add_zero] using htree
  have hforest : K.graph.IsAcyclic :=
    induced_pairBall_acyclic_of_ambient_tree g.graph S root root r 0 (by simp) htree'
  have hKzero : ∀ v,K.deficit v=0 := by
    intro v
    apply hzero v.val.val
    have hh := (f v).property
    simpa only [Nat.add_zero] using hh
  have hh := K.extensionGreen_zero_deficit_forest_diagonal hd hKzero hforest
    (pairBallLeft M.graph root root r) m z hm hz hmim
  have heq : pairBallRight M.graph root root r=pairBallLeft M.graph root root r := Subtype.ext rfl
  change K.extensionGreen m z _ _=_
  rw [heq]
  exact hh

theorem restrict_P_adjacent_of_ambient_tree (g : DeficientGraph V d) (hd : 3≤d)
    (S : Set V) (u v : S) (huv : g.graph.Adj u.val v.val) (r : ℕ)
    (htree : (graphBall g.graph u.val (r+1)).IsTree)
    (hzero : ∀ w∈graphBallVertices g.graph u.val (r+1),g.deficit w=0)
    (m z : ℂ) (hm : m^2+z*m+1=0) (hz : 0<z.im) (hmim : 0 ≤ m.im) :
    (g.restrict S).P r z m u v=kestenMcKayTransform d m z*(-m*treeEdgeWeight d) := by
  let M := g.restrict S
  let A := pairBallVertices M.graph u v r
  let K := M.restrict A
  have hcenters : g.graph.edist u.val v.val≤(1:ℕ∞) := (SimpleGraph.edist_eq_one_iff_adj.mpr huv).le
  let f := inducedPairBallAmbientMap g.graph S u v r 1 hcenters
  have hforest : K.graph.IsAcyclic :=
    induced_pairBall_acyclic_of_ambient_tree g.graph S u v r 1 hcenters htree
  have hKzero : ∀ w,K.deficit w=0 := fun w => hzero w.val.val (f w).property
  exact K.extensionGreen_zero_deficit_forest_adjacent hd hKzero hforest
    (pairBallLeft M.graph u v r) (pairBallRight M.graph u v r) huv m z hm hz hmim

end DeficientGraph
end LocalLaw
