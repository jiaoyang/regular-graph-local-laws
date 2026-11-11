import SpectralConsequences.CavityBallColumns
import LocalLaw.CavityMinorModelBounds

/-! Active original cut labels are exactly the cut labels of the true
neighbor-deleted cavity ball. The removed branch is handled by membership. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance cavityBoundaryActiveDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}

def cavityBoundaryInnerDeleted (g:LocalLaw.RegularGraph N d)(o:Fin N)(ell:ℕ)(hell:2≤ell)
    (j:graphBallVertices g.graph o ell)(hjo:g.graph.Adj j.val o)
    (e:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)):{v:Fin N//v≠j.val}:=
  ⟨e.val.1,fun he=>(g.truncatedCavityBoundaryInner o ell hell j hjo e).property (Subtype.ext he)⟩

def ActiveCavityBoundary (g:LocalLaw.RegularGraph N d)(o:Fin N)(ell:ℕ)(hell:2≤ell)
    (j:graphBallVertices g.graph o ell)(hjo:g.graph.Adj j.val o):=
  {e:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)//
    cavityBoundaryInnerDeleted g o ell hell j hjo e∈
      graphBallVertices (g.deficient.deleteVertex j.val).graph ⟨o,hjo.ne.symm⟩ ell}

instance activeCavityBoundaryFintype (g:LocalLaw.RegularGraph N d)(o:Fin N)(ell:ℕ)(hell:2≤ell)
    (j:graphBallVertices g.graph o ell)(hjo:g.graph.Adj j.val o):
    Fintype (ActiveCavityBoundary g o ell hell j hjo):=by unfold ActiveCavityBoundary;infer_instance

/-- Literal cut-edge equivalence; closure of the retained tree branch rules
out any new cavity boundary edge whose outer endpoint was still in T. -/
def activeCavityBoundaryEquiv (g:LocalLaw.RegularGraph N d)(o:Fin N)(ell:ℕ)(hell:2≤ell)
    (j:graphBallVertices g.graph o ell)(hjo:g.graph.Adj j.val o)
    (hTree:(graphBall g.graph o (ell+1)).IsTree):
    ActiveCavityBoundary g o ell hell j hjo ≃
      BoundaryOrientedEdge (g.deficient.deleteVertex j.val).graph
        (graphBallVertices (g.deficient.deleteVertex j.val).graph ⟨o,hjo.ne.symm⟩ ell) where
  toFun e:=⟨(cavityBoundaryInnerDeleted g o ell hell j hjo e.val,
      ⟨e.val.val.2,fun he=>e.val.property.2.2 (by rw [he];exact j.property)⟩),
    e.val.property.1,e.property,fun hb=>e.val.property.2.2
      ((graphHom_edist_le (SimpleGraph.Embedding.induce (G:=g.graph) {v|v≠j.val}).toHom
        ⟨o,hjo.ne.symm⟩ ⟨e.val.val.2,fun he=>e.val.property.2.2 (by rw [he];exact j.property)⟩).trans hb)⟩
  invFun e:=
    let hb:e.val.2.val∉graphBallVertices g.graph o ell:=fun hv=>
      e.property.2.2 (tree_deleted_ball_closed_in_root_ball g.graph j.val o ell hjo hTree e.property.2.1 hv e.property.1)
    ⟨⟨(e.val.1.val,e.val.2.val),e.property.1,
      (graphHom_edist_le (SimpleGraph.Embedding.induce (G:=g.graph) {v|v≠j.val}).toHom
        ⟨o,hjo.ne.symm⟩ e.val.1).trans e.property.2.1,hb⟩,
      by
        have he:cavityBoundaryInnerDeleted g o ell hell j hjo
          ⟨(e.val.1.val,e.val.2.val),e.property.1,
            (graphHom_edist_le (SimpleGraph.Embedding.induce (G:=g.graph) {v|v≠j.val}).toHom
              ⟨o,hjo.ne.symm⟩ e.val.1).trans e.property.2.1,hb⟩=e.val.1:=Subtype.ext rfl
        rw [he]
        exact e.property.2.1⟩
  left_inv e:=by apply Subtype.ext;apply Subtype.ext;rfl
  right_inv e:=by apply Subtype.ext;apply Prod.ext <;> apply Subtype.ext <;> rfl

theorem activeCavityBoundary_card (g:LocalLaw.RegularGraph N d)(hd:3≤d)(o:Fin N)(ell:ℕ)(hell:2≤ell)
    (j:graphBallVertices g.graph o ell)(hjo:g.graph.Adj j.val o)
    (hTree:(graphBall g.graph o (ell+1)).IsTree):
    Nat.card (ActiveCavityBoundary g o ell hell j hjo)=(d-1)^(ell+1):=by
  rw [Nat.card_congr (activeCavityBoundaryEquiv g o ell hell j hjo hTree)]
  exact deleted_tree_ball_boundary_card g hd j.val o ell (by omega) hjo hTree

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.activeCavityBoundary_card
