import LocalLaw.DeletedLeafBallGeometry
import LocalLaw.PartialFirstDeletionCaps
import LocalLaw.PartialSampleTreeTail

/-! # Actual eligible sampled-first leaf geometry in every old restriction

The source I/J tests imply the tree, zero-deficit and separated-leaf inputs
needed for scalar covariance. The restriction is arbitrary: it need not
contain any ambient endpoint ball.
-/

noncomputable section
set_option maxHeartbeats 1600000
namespace LocalLaw
local instance selectedFirstLeafGeometryDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V:Type}[Fintype V]{d:ℕ}

theorem restricted_ball_tree_zero_of_ambient (g:DeficientGraph V d)(S:Set V)(b:S)(r:ℕ)
    (htree:(graphBall g.graph b.val r).IsTree)
    (hzero:∀v∈graphBallVertices g.graph b.val r,g.deficit v=0) :
    (graphBall (g.restrict S).graph b r).IsTree ∧
      ∀v∈graphBallVertices (g.restrict S).graph b r,(g.restrict S).deficit v=0 := by
  let f:graphBall (g.restrict S).graph b r→g graphBall g.graph b.val r:=
    {toFun:=fun v=>⟨v.val.val,(ambient_edist_le_induced_edist g.graph S b v.val).trans v.property⟩
     map_rel':=fun h=>h}
  have hf:Function.Injective f:=by
    intro v w h
    have hv:v.val.val=w.val.val:=congrArg (fun a:graphBallVertices g.graph b.val r=>a.val) h
    exact Subtype.ext (Subtype.ext hv)
  constructor
  · exact ⟨graphBall_connected _ _ _,fun a p hp=>htree.IsAcyclic (p.map f) (hp.map hf)⟩
  · intro v hv
    exact hzero v.val ((ambient_edist_le_induced_edist g.graph S b v).trans hv)

end DeficientGraph
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

omit [Fintype ι] in
theorem partialFirst_leaf_geometry (g:RegularGraph N d)(hd:1≤d)
    (T:Set (Fin N))(labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector r:ℕ)(hsep:2*r+1≤selector)(S:Set (Tᶜ:Set (Fin N))) :
    let s:=g.admissibleState T labels samples
    let M:=(g.deficient.delete T).restrict S
    let B:=s.partialFirstRemovedSet selector S
    let H:=M.deletedLeafModel hd B
    (∀l:DeletedLeafIndex M.graph B,(graphBall H.graph (.inr l) r).IsTree) ∧
    (∀l:DeletedLeafIndex M.graph B,∀v∈graphBallVertices H.graph (.inr l) r,H.deficit v=0) ∧
    (∀l m:DeletedLeafIndex M.graph B,l≠m→((2*r:ℕ):ℕ∞)<H.graph.edist (.inr l) (.inr m)) := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let M:=(g.deficient.delete T).restrict S
  let B:=s.partialFirstRemovedSet selector S
  have hb (b:B)(R:ℕ)(hR:R+1≤selector) :
      (graphBall M.graph b.val R).IsTree ∧
        ∀v∈graphBallVertices M.graph b.val R,M.deficit v=0 := by
    obtain ⟨i,hi⟩:=b.property
    have hg:=g.eligible_sample_root_tree_zero_ball T labels samples selector R hR i b.val.val (Or.inl hi.symm)
    exact (g.deficient.delete T).restricted_ball_tree_zero_of_ambient S b.val R hg.1 hg.2
  have hbsep (b c:B)(hne:b≠c) :
      ((2*r:ℕ):ℕ∞)<M.graph.edist b.val c.val := by
    have hne':b.val.val≠c.val.val:=fun h=>hne (Subtype.ext (Subtype.ext h))
    have hh:=s.selectedFirstSet_separated selector b.val.val b.property c.val.val c.property hne'
    exact ((ENat.coe_le_coe.mpr (by omega:2*r≤selector)).trans_lt hh).trans_le
      (ambient_edist_le_induced_edist (outsideGraph g.graph T) S b.val c.val)
  refine ⟨?_,?_,?_⟩
  · intro l
    exact M.deletedLeafModel_ball_isTree hd B l r (hb l.2.val r (by omega)).1
  · intro l
    exact M.deletedLeafModel_ball_zero_deficit hd B l r (hb l.2.val r (by omega)).2
  · intro l m hne
    exact deletedLeafGraph_leaf_separated M.graph B (2*r) hbsep
      (fun b=>(hb b (2*r) hsep).1) l m hne

end RegularGraph
end LocalLaw
