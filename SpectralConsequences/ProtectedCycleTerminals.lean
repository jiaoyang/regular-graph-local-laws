import SpectralConsequences.ParentEvenLocalization
import SpectralConsequences.ProtectedBranches
import SpectralConsequences.ProtectedPatchEdges

/-! Old-edge localization of each genuine connected even generator in a
protected switched ball. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace SpectralConsequences
open LocalLaw
local instance protectedCycleTerminalsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type*}[Fintype V]{T:Set V}{ι:Type*}[Fintype ι]
variable {s:LocalLaw.LabelledResamplingState V T ι}{selector R:ℕ}

omit [Fintype V] in
theorem ProtectedPatches.old_edge_of_away (_h:ProtectedPatches s selector R)
    {x y:V}(hxy:(s.fullResample selector).graph.Adj x y)
    (hx:∀i,x≠(s.quad i).c ∧x≠(s.quad i).d)
    (hy:∀i,y≠(s.quad i).c ∧y≠(s.quad i).d):s.graph.Adj x y:=by
  by_contra hnot
  obtain ⟨i,_,hh⟩:=fullResample_new_edge_cases s selector hxy hnot
  rcases hh with hh|hh|hh|hh
  · exact (hy i).2 hh.2
  · exact (hx i).2 hh.1
  · exact (hy i).1 hh.2
  · exact (hx i).1 hh.1

theorem ProtectedPatches.even_old_edges (h:ProtectedPatches s selector R)(center:V)
    (C:EvenEdgeSubgraph (graphBall (s.fullResample selector).graph center R)):
    C.val.map (⟨Subtype.val,Subtype.val_injective⟩:
      graphBallVertices (s.fullResample selector).graph center R↪V)≤s.graph:=by
  intro x y hxy
  obtain ⟨a,b,hab,rfl,rfl⟩:=(SimpleGraph.map_adj _ C.val x y).mp hxy
  apply h.old_edge_of_away (C.property.1 hab)
  · intro i
    exact ⟨fun he=>h.ball_even_avoids_sample i center C a (Or.inl he)
      ((C.val.mem_support).mpr ⟨b,hab⟩),
      fun he=>h.ball_even_avoids_sample i center C a (Or.inr he)
      ((C.val.mem_support).mpr ⟨b,hab⟩)⟩
  · intro i
    exact ⟨fun he=>h.ball_even_avoids_sample i center C b (Or.inl he)
      ((C.val.mem_support).mpr ⟨a,hab.symm⟩),
      fun he=>h.ball_even_avoids_sample i center C b (Or.inr he)
      ((C.val.mem_support).mpr ⟨a,hab.symm⟩)⟩

theorem ProtectedPatches.even_parent_old (h:ProtectedPatches s selector R)(center:V)
    (C:EvenEdgeSubgraph (graphBall (s.fullResample selector).graph center R)):
    ∀x∈C.val.support,∀y∈C.val.support,
      (ballHeightParentData (s.fullResample selector).graph center R).tree.Adj x y→
      s.graph.Adj x.val y.val:=by
  intro x hx y hy hxy
  apply h.old_edge_of_away
    ((ballHeightParentData _ center R).tree_le _ (ballHeightParentData_parent_adj _ center R) hxy)
  · intro i
    exact ⟨fun he=>h.ball_even_avoids_sample i center C x (Or.inl he) hx,
      fun he=>h.ball_even_avoids_sample i center C x (Or.inr he) hx⟩
  · intro i
    exact ⟨fun he=>h.ball_even_avoids_sample i center C y (Or.inl he) hy,
      fun he=>h.ball_even_avoids_sample i center C y (Or.inr he) hy⟩

theorem ProtectedPatches.even_generator_old_ball (h:ProtectedPatches s selector R)
    (center:V)(F:EvenEdgeSubgraph (graphBall (s.fullResample selector).graph center R))
    (hconn:((ballHeightParentData (s.fullResample selector).graph center R).tree.induce F.val.support).Connected)
    (v:graphBallVertices (s.fullResample selector).graph center R)(hv:v∈F.val.support):
    ∀w∈F.val.support,w.val∈graphBallVertices s.graph
      (ParentCut.terminal (ballHeightParentData (s.fullResample selector).graph center R)
        s.graph Subtype.val v).val R:=by
  exact ParentCut.connected_support_old_ball _ s.graph Subtype.val R
    (ballVertexHeight_le _ center R) _ hconn (h.even_parent_old center F) v hv

theorem ProtectedPatches.even_generator_zero_if_terminal_near (h:ProtectedPatches s selector R)
    (center:V)(F:EvenEdgeSubgraph (graphBall (s.fullResample selector).graph center R))
    (hconn:((ballHeightParentData (s.fullResample selector).graph center R).tree.induce F.val.support).Connected)
    (v:graphBallVertices (s.fullResample selector).graph center R)(hv:v∈F.val.support)
    (i:ι)(side:Bool)
    (hnear:s.graph.edist (samplePort s i side)
      (ParentCut.terminal (ballHeightParentData (s.fullResample selector).graph center R)
        s.graph Subtype.val v).val≤(R:ℕ∞)):F.val=⊥:=by
  apply ParentCut.even_eq_bot_of_map_forest F.val
    (⟨Subtype.val,Subtype.val_injective⟩:
      graphBallVertices (s.fullResample selector).graph center R↪V)
    s.graph (protectedPatch s R i) (h.even_old_edges center F) F.property.2 ?_ (h.tree i).IsAcyclic
  intro x hx
  obtain ⟨y,hxy⟩:=((F.val.map (⟨Subtype.val,Subtype.val_injective⟩:_↪V)).mem_support).mp hx
  obtain ⟨a,b,hab,rfl,rfl⟩:=(SimpleGraph.map_adj _ F.val x y).mp hxy
  exact old_ball_subset_patch s R i side _ hnear
    (h.even_generator_old_ball center F hconn v hv a ((F.val.mem_support).mpr ⟨b,hab⟩))

end LabelledResamplingState
end SpectralConsequences
