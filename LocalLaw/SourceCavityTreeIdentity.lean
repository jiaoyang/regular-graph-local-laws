import LocalLaw.HomogeneousCavityBall
import LocalLaw.DeletedTreeBallGeometry
import LocalLaw.SourceSingletonGeometry

/-!
# Actual sampled tree models equal the scalar cavity iterate

The original good ball, actual far-boundary condition and regular degree law
derive the cavity tree, one-root deficit and exact homogeneous branching.
The physical finite inverse then equals the scalar cavity iteration for all
upper-half-plane z and boundary q with nonnegative imaginary part.
-/

noncomputable section
namespace LocalLaw
local instance sourceCavityTreeDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*}

theorem outside_ball_isTree (G : SimpleGraph V) (T : Set V)
    (c : (Tᶜ : Set V)) (r : ℕ) (hTree : (graphBall G c.val r).IsTree) :
    (graphBall (outsideGraph G T) c r).IsTree := by
  let f : graphBall (outsideGraph G T) c r →g graphBall G c.val r :=
    { toFun := fun v => ⟨v.val.val, (graphHom_edist_le
        (SimpleGraph.Embedding.induce (G := G) Tᶜ).toHom c v.val).trans v.property⟩
      map_rel' := fun h => h }
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun v : graphBallVertices G c.val r => v.val) h))
  refine ⟨graphBall_connected _ _ _, ?_⟩
  intro v p hp
  exact hTree.IsAcyclic (p.map f) (hp.map hf)

namespace RegularGraph
variable {N d : ℕ}

theorem deleted_degree_deficit_saturated (g : RegularGraph N d) (T : Set (Fin N))
    (v : (Tᶜ : Set (Fin N))) :
    (g.deficient.delete T).graph.degree v + (g.deficient.delete T).deficit v = d := by
  rw [g.deficient.delete_degree_deficit_sum]
  change g.graph.degree v.val + 0 = d
  simpa only [Nat.add_zero] using g.regular v.val

/-- The actual finite model at a sampled cavity edge is exactly Y_r(q).
All tree and source deficit data are derived from the original graph. -/
theorem source_cavity_tree_identity (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (b c : (Tᶜ : Set (Fin N)))
    (hbc : (outsideGraph g.graph T).Adj b c) (r : ℕ)
    (hTree : (graphBall g.graph c.val (r + 1)).IsTree)
    (hfar : ∀ α : BoundaryOrientedEdge g.graph T,
      ((r + 2 : ℕ) : ℕ∞) < (outsideGraph g.graph T).edist b (boundaryOuterEndpoint g.graph T α))
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    ((g.deficient.delete T).deleteVertex b).P r z q
      ⟨c, hbc.ne.symm⟩ ⟨c, hbc.ne.symm⟩ = cavityIterate z q (r + 1) := by
  let D := g.deficient.delete T
  let cc : {v : (Tᶜ : Set (Fin N)) // v ≠ b} := ⟨c, hbc.ne.symm⟩
  have hcommon : (graphBall D.graph c (r + 1)).IsTree := outside_ball_isTree g.graph T c (r + 1) hTree
  have hzero : ∀ v ∈ graphBallVertices D.graph c (r + 1), D.deficit v = 0 := by
    intro v hv
    exact g.singleton_common_ball_zero_deficit T b c hbc r hfar v hv
  have hlocalTree : (graphBall (D.deleteVertex b).graph cc r).IsTree :=
    deleted_ball_isTree D.graph b cc r hcommon
  have hdef : ∀ v ∈ graphBallVertices (D.deleteVertex b).graph cc r,
      (D.deleteVertex b).deficit v = if v = cc then 1 else 0 := by
    intro v hv
    exact D.deleted_tree_ball_one_root_deficit b cc hbc r hcommon hzero ⟨v, hv⟩
  have hsat : ∀ v ∈ graphBallVertices (D.deleteVertex b).graph cc r,
      (D.deleteVertex b).graph.degree v + (D.deleteVertex b).deficit v = d := by
    intro v _
    exact (D.deleteVertex_degree_deficit_sum b v).trans (g.deleted_degree_deficit_saturated T v.val)
  exact (D.deleteVertex b).homogeneous_cavity_P_diagonal hd cc r hlocalTree hdef hsat q z hz hq

end RegularGraph
end LocalLaw
