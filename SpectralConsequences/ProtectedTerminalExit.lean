import SpectralConsequences.ProtectedCycleTerminals
import SpectralConsequences.ProtectedPortPaths

/-! A nonroot terminal supporting an actual cycle is an attachment reached
from one uniquely determined protected old branch. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace SpectralConsequences
open LocalLaw
local instance protectedTerminalExitDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type*}[Fintype V]{T:Set V}{ι:Type*}[Fintype ι]
variable {s:LocalLaw.LabelledResamplingState V T ι}{selector R:ℕ}

theorem ProtectedPatches.terminal_exit (h:ProtectedPatches s selector R)
    (center:V)(F:EvenEdgeSubgraph (graphBall (s.fullResample selector).graph center R))
    (hconn:((ballHeightParentData (s.fullResample selector).graph center R).tree.induce F.val.support).Connected)
    (v:graphBallVertices (s.fullResample selector).graph center R)(hv:v∈F.val.support)
    (hne:F.val≠⊥)
    (htnot:ParentCut.terminal (ballHeightParentData (s.fullResample selector).graph center R)
      s.graph Subtype.val v≠(ballHeightParentData (s.fullResample selector).graph center R).root):
    ∃i:ι,∃side:Bool,
      (ParentCut.terminal (ballHeightParentData (s.fullResample selector).graph center R)
        s.graph Subtype.val v).val=sampleAnchor s i side ∧
      ∃hc:center∈protectedPatch s R i,∃q:(protectedBranchGraph s R i).Walk
        ⟨samplePort s i side,samplePort_mem s R i side⟩ ⟨center,hc⟩,q.length≤R:=by
  let D:=ballHeightParentData (s.fullResample selector).graph center R
  let t:=ParentCut.terminal D s.graph Subtype.val v
  have hstop:¬s.graph.Adj t.val (D.parent ⟨t,htnot⟩).val:=by
    rcases ParentCut.terminal_stop D s.graph Subtype.val v with hr|⟨ht,hs⟩
    · exact False.elim (htnot hr)
    · exact hs
  have hAdj:(s.fullResample selector).graph.Adj t.val (D.parent ⟨t,htnot⟩).val:=
    ballHeightParentData_parent_adj _ center R ⟨t,htnot⟩
  have hexit (i:ι)(side:Bool)(ha:t.val=sampleAnchor s i side)
      (hb:(D.parent ⟨t,htnot⟩).val=samplePort s i side):
      ∃i:ι,∃side:Bool,t.val=sampleAnchor s i side ∧
        ∃hc:center∈protectedPatch s R i,∃q:(protectedBranchGraph s R i).Walk
          ⟨samplePort s i side,samplePort_mem s R i side⟩ ⟨center,hc⟩,q.length≤R:=by
    let f:D.tree→g (s.fullResample selector).graph:=
      {toFun:=Subtype.val,map_rel':=fun hab=>
        D.tree_le _ (ballHeightParentData_parent_adj _ center R) hab}
    have hf:Function.Injective f:=Subtype.val_injective
    obtain ⟨p,hentry,hpath,hlen⟩:=ParentCut.mapped_root_path_before_parent D _ f hf t htnot
      (sampleAnchor s i side) (samplePort s i side) ha hb
    have hlenR:p.length≤R:=by
      have hh:=ballVertexHeight_le (s.fullResample selector).graph center R t
      change D.height t≤R at hh
      omega
    obtain ⟨hc,q,hq⟩:=h.path_before_port i side p hentry hpath hlenR
    exact ⟨i,side,ha,hc,q,hq⟩
  have hport (i:ι)(side:Bool)(ht:t.val=samplePort s i side):False:=by
    apply hne
    apply h.even_generator_zero_if_terminal_near center F hconn v hv i side
    change s.graph.edist (samplePort s i side) t.val≤(R:ℕ∞)
    rw [ht]
    simp
  obtain ⟨i,_,hi⟩:=fullResample_new_edge_cases s selector hAdj hstop
  rcases hi with hi|hi|hi|hi
  · exact hexit i true hi.1 hi.2
  · exact False.elim (hport i true hi.1)
  · exact hexit i false hi.1 hi.2
  · exact False.elim (hport i false hi.1)

end LabelledResamplingState
end SpectralConsequences
