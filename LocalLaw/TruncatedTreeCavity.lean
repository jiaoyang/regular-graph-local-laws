import LocalLaw.TreePairCutRadius
import LocalLaw.SourceCavityTreeIdentity
import LocalLaw.DetachedEndpointModel

/-! # The literal neighbor-deleted truncated root model is a cavity iterate

The retained root component after deletion of a neighboring vertex is the
actual deleted radius ball. Its isolation and the deficit-preserving model
isomorphism are proved, so no minor-model identity is an assumption.
-/

noncomputable section
set_option maxHeartbeats 2600000
namespace LocalLaw
local instance truncatedTreeCavityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

theorem adjacent_pairBall_isTree_of_root_ball (G : SimpleGraph V) (j o : V) (ell : ℕ)
    (hjo : G.Adj j o) (hTree : (graphBall G o (ell + 1)).IsTree) :
    (pairBallGraph G j o ell).IsTree := by
  have hsub : pairBallVertices G j o ell ⊆ graphBallVertices G o (ell + 1) := by
    intro v hv
    rcases hv with hv | hv
    · exact adjacent_ball_subset_succ G hjo ell hv
    · exact graphBallVertices_mono G o (Nat.le_succ ell) hv
  let f := G.induceHomOfLE hsub
  constructor
  · exact pairBall_connected_of_adj G hjo ell
  · intro v p hp
    exact hTree.IsAcyclic (p.map f.toHom) (hp.map f.injective)

theorem tree_deleted_ball_closed_in_root_ball (G : SimpleGraph V) (j o : V) (ell : ℕ)
    (hjo : G.Adj j o) (hTree : (graphBall G o (ell + 1)).IsTree)
    {x y : {v : V // v ≠ j}}
    (hx : x ∈ graphBallVertices (G.induce {v | v ≠ j}) ⟨o, hjo.ne.symm⟩ ell)
    (hy : y.val ∈ graphBallVertices G o ell) (hxy : (G.induce {v | v ≠ j}).Adj x y) :
    y ∈ graphBallVertices (G.induce {v | v ≠ j}) ⟨o, hjo.ne.symm⟩ ell := by
  let W := pairBallVertices G j o ell
  let H := pairBallGraph G j o ell
  let jj := pairBallLeft G j o ell
  let oo := pairBallRight G j o ell
  have heq := tree_pair_second_branch_eq_deleted_ball G j o ell hjo
    (adjacent_pairBall_isTree_of_root_ball G j o ell hjo hTree)
  have hxC : x.val ∈ inducedTreeBranch G W jj oo oo := by
    rw [heq]
    exact ⟨⟨x, hx⟩, rfl⟩
  let xx : W := ⟨x.val, inducedTreeBranch_subset G W jj oo oo hxC⟩
  let yy : W := ⟨y.val, Or.inr hy⟩
  have hnot : ¬(SimpleGraph.edge jj oo).Adj xx yy := by
    intro he
    rcases (SimpleGraph.edge_adj _ _ _ _).mp he with ⟨⟨hxj, _⟩ | ⟨_, hyj⟩, _⟩
    · exact x.property (congrArg Subtype.val hxj)
    · exact y.property (congrArg Subtype.val hyj)
  have hr := (mem_treeEdgeBranch_iff H jj oo oo xx).mp
    ((mem_inducedTreeBranch_iff G W jj oo oo xx).mp hxC)
  have hyC : y.val ∈ inducedTreeBranch G W jj oo oo :=
    (mem_inducedTreeBranch_iff G W jj oo oo yy).mpr
      ((mem_treeEdgeBranch_iff H jj oo oo yy).mpr (hr.trans (show (treeEdgeDeleted H jj oo).Adj xx yy from
        ⟨hxy, hnot⟩).reachable))
  rw [heq] at hyC
  obtain ⟨v, hv⟩ := hyC
  have he : v.val = y := Subtype.ext hv
  exact Eq.mp (congrArg (fun z => z ∈ graphBallVertices (G.induce {v | v ≠ j}) ⟨o, hjo.ne.symm⟩ ell) he) v.property

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

def restrictDeleteVertexIso (g : DeficientGraph V d) (T : Set V) (j : T) :
    ((g.restrict T).deleteVertex j).graph ≃g
      ((g.deleteVertex j.val).restrict {v | v.val ∈ T}).graph where
  toEquiv :=
    { toFun := fun v => ⟨⟨v.val.val, fun he => v.property (Subtype.ext he)⟩, v.val.property⟩
      invFun := fun v => ⟨⟨v.val.val, v.property⟩, fun he => v.val.property (congrArg Subtype.val he)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := Iff.rfl

theorem restrictDeleteVertex_deficit (g : DeficientGraph V d) (T : Set V) (j : T)
    (v : {v : T // v ≠ j}) :
    ((g.restrict T).deleteVertex j).deficit v =
      ((g.deleteVertex j.val).restrict {v | v.val ∈ T}).deficit (g.restrictDeleteVertexIso T j v) := by
  change ((g.restrict T).deleteVertex j).deficit v =
    (g.deleteVertex j.val).deficit (g.restrictDeleteVertexIso T j v).val
  rw [(g.restrict T).deleteVertex_deficit_eq_adj, g.deleteVertex_deficit_eq_adj]
  rfl

end DeficientGraph

namespace RegularGraph
variable {N d : ℕ}

theorem deleted_root_ball_cavity_diagonal (g : RegularGraph N d) (hd : 3 ≤ d)
    (j o : Fin N) (ell : ℕ) (hjo : g.graph.Adj j o)
    (hTree : (graphBall g.graph o (ell + 1)).IsTree)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let D := g.deficient.deleteVertex j
    let root : {v : Fin N // v ≠ j} := ⟨o, hjo.ne.symm⟩
    (D.restrict (graphBallVertices D.graph root ell)).extensionGreen q z
      (cavityBallRoot D.graph root ell) (cavityBallRoot D.graph root ell) = cavityIterate z q (ell + 1) := by
  dsimp only
  let root : {v : Fin N // v ≠ j} := ⟨o, hjo.ne.symm⟩
  have ht := deleted_ball_isTree g.graph j root ell hTree
  have hδ := g.deficient.deleted_tree_ball_one_root_deficit j root hjo ell hTree (fun _ _ => rfl)
  have hsat : ∀ v ∈ graphBallVertices (g.deficient.deleteVertex j).graph root ell,
      (g.deficient.deleteVertex j).graph.degree v + (g.deficient.deleteVertex j).deficit v = d := by
    intro v _
    have hh := g.deficient.deleteVertex_degree_deficit_sum j v
    change _ = g.graph.degree v.val + 0 at hh
    simpa only [g.regular v.val, add_zero] using hh
  exact (g.deficient.deleteVertex j).homogeneous_cavity_ball_diagonal hd root ell ht
    (fun v hv => hδ ⟨v, hv⟩) hsat q z hz hq

/-- The exact reference value for the actual neighbor-deleted Ext(T,q)
model. With T radius ell, the iteration index is ell+1. -/
theorem truncated_neighbor_cavity_diagonal (g : RegularGraph N d) (hd : 3 ≤ d) (o : Fin N)
    (ell : ℕ) (j : graphBallVertices g.graph o ell) (hjo : g.graph.Adj j.val o)
    (hTree : (graphBall g.graph o (ell + 1)).IsTree)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let T := graphBallVertices g.graph o ell
    let root : {v : T // v ≠ j} :=
      ⟨⟨o, center_mem_graphBall g.graph o ell⟩, fun he => hjo.ne.symm (congrArg Subtype.val he)⟩
    ((g.deficient.restrict T).deleteVertex j).extensionGreen q z root root = cavityIterate z q (ell + 1) := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let D := g.deficient.deleteVertex j.val
  let A : Set {v : Fin N // v ≠ j.val} := {v | v.val ∈ T}
  let rootD : {v : Fin N // v ≠ j.val} := ⟨o, hjo.ne.symm⟩
  let B := graphBallVertices D.graph rootD ell
  let L := (g.deficient.restrict T).deleteVertex j
  let M := D.restrict A
  let rootL : {v : T // v ≠ j} :=
    ⟨⟨o, center_mem_graphBall g.graph o ell⟩, fun he => hjo.ne.symm (congrArg Subtype.val he)⟩
  let e := g.deficient.restrictDeleteVertexIso T j
  have hBA : B ⊆ A := by
    intro v hv
    exact (graphHom_edist_le (SimpleGraph.Embedding.induce (G := g.graph) {v | v ≠ j.val}).toHom rootD v).trans hv
  let F : Set A := {v | v.val ∈ B}
  let rootF : F := ⟨e rootL, center_mem_graphBall _ _ _⟩
  let eB : (M.restrict F).graph ≃g (D.restrict B).graph := inducePreimageIso D.graph A B hBA
  have hcut : ∀ x ∈ F, ∀ y ∉ F, ¬M.graph.Adj x y := by
    intro x hx y hy hxy
    exact hy (tree_deleted_ball_closed_in_root_ball g.graph j.val o ell hjo hTree hx y.property hxy)
  have hmodel := M.extensionGreen_iso L e (g.deficient.restrictDeleteVertex_deficit T j) q z
  have hmodelEntry : M.extensionGreen q z (e rootL) (e rootL) = L.extensionGreen q z rootL rootL :=
    congrFun (congrFun hmodel rootL) rootL
  have hblock := M.restrict_extensionGreen_of_isolated hd F hcut q z hz hq
  have hblockEntry : (M.restrict F).extensionGreen q z rootF rootF = M.extensionGreen q z (e rootL) (e rootL) :=
    congrFun (congrFun hblock rootF) rootF
  have hball := (D.restrict B).extensionGreen_iso (M.restrict F) eB (fun _ => rfl) q z
  have hballEntry := congrFun (congrFun hball rootF) rootF
  exact hmodelEntry.symm.trans (hblockEntry.symm.trans (hballEntry.symm.trans
    (g.deleted_root_ball_cavity_diagonal hd j.val o ell hjo hTree q z hz hq)))

end RegularGraph
end LocalLaw
