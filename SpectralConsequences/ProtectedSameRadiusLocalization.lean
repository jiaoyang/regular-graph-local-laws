import SpectralConsequences.ProtectedTerminalExit
import SpectralConsequences.ConnectedCycleTransfer

/-! All connected fundamental cycle generators in a protected switched ball
are contained in ONE old ball of exactly the same radius. -/
noncomputable section
set_option maxHeartbeats 2500000
namespace SpectralConsequences
open LocalLaw
local instance protectedSameRadiusLocalizationDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type*}[Fintype V]{T:Set V}{ι:Type*}[Fintype ι]
variable {s:LocalLaw.LabelledResamplingState V T ι}{selector R:ℕ}

theorem ProtectedPatches.same_radius_generator_localization (h:ProtectedPatches s selector R)
    (center:V):∃anchor:V,
    ∀F:EvenEdgeSubgraph (graphBall (s.fullResample selector).graph center R),
      ((ballHeightParentData (s.fullResample selector).graph center R).tree.induce F.val.support).Connected→
      ∀w∈F.val.support,w.val∈graphBallVertices s.graph anchor R:=by
  let D:=ballHeightParentData (s.fullResample selector).graph center R
  let term:=ParentCut.terminal D s.graph Subtype.val
  have hne (F:EvenEdgeSubgraph (graphBall (s.fullResample selector).graph center R))
      (v:graphBallVertices (s.fullResample selector).graph center R)(hv:v∈F.val.support):F.val≠⊥:=by
    intro hbot
    obtain ⟨w,hw⟩:=(F.val.mem_support).mp hv
    rw [hbot] at hw
    exact hw
  by_cases hex:∃F:EvenEdgeSubgraph (graphBall (s.fullResample selector).graph center R),
      (D.tree.induce F.val.support).Connected ∧
      ∃v:graphBallVertices (s.fullResample selector).graph center R,v∈F.val.support ∧term v≠D.root
  · obtain ⟨F,hconn,v,hv,ht⟩:=hex
    obtain ⟨i,side,ha,hc,q,hq⟩:=h.terminal_exit center F hconn v hv (hne F v hv) ht
    refine ⟨sampleAnchor s i side,?_⟩
    intro K hK
    obtain ⟨w⟩:=hK.nonempty
    let u:=w.val
    have hu:u∈K.val.support:=w.property
    by_cases hroot:term u=D.root
    · have hnear:s.graph.edist (samplePort s i side) (term u).val≤(R:ℕ∞):=by
        rw [hroot]
        exact protectedBranch_distance s R i side center hc q hq
      exact False.elim ((hne K u hu)
        (h.even_generator_zero_if_terminal_near center K hK u hu i side hnear))
    · obtain ⟨j,side',ha',hc',q',hq'⟩:=h.terminal_exit center K hK u hu (hne K u hu) hroot
      obtain ⟨hij,hside⟩:=ProtectedPatches.branch_unique s selector R h center i j side side'
        hc hc' q.reachable q'.reachable
      subst j
      subst side'
      intro x hx
      have hloc:=h.even_generator_old_ball center K hK u hu x hx
      simpa only [ha'] using hloc
  · refine ⟨center,?_⟩
    intro F hF
    obtain ⟨v⟩:=hF.nonempty
    have ht:term v.val=D.root:=by
      by_contra hnot
      exact hex ⟨F,hF,v.val,v.property,hnot⟩
    intro x hx
    have hloc:=h.even_generator_old_ball center F hF v.val v.property x hx
    change x.val∈graphBallVertices s.graph (term v.val).val R at hloc
    simpa only [ht] using hloc

theorem ProtectedPatches.same_radius_excess (h:ProtectedPatches s selector R)
    (ω:ℕ)(hOld:∀x:V,graphExcess (graphBall s.graph x R)≤ω)(center:V):
    graphExcess (graphBall (s.fullResample selector).graph center R)≤ω:=by
  obtain ⟨anchor,hlocal⟩:=h.same_radius_generator_localization center
  let B:=graphBall (s.fullResample selector).graph center R
  let D:=ballHeightParentData (s.fullResample selector).graph center R
  have hDB:D.tree≤B:=D.tree_le _ (ballHeightParentData_parent_adj _ center R)
  have hexcess:=excess_le_of_connected_generators B D hDB (graphBall_connected _ center R)
    s.graph (⟨Subtype.val,Subtype.val_injective⟩:
      graphBallVertices (s.fullResample selector).graph center R↪V)
    (graphBallVertices s.graph anchor R) (h.even_old_edges center) hlocal
  exact hexcess.trans (hOld anchor)

theorem ProtectedPatches.same_radius_root_tree (h:ProtectedPatches s selector R)
    (center:V)(hcenter:center∈T)(hOld:(graphBall s.graph center R).IsTree):
    (graphBall (s.fullResample selector).graph center R).IsTree:=by
  let B:=graphBall (s.fullResample selector).graph center R
  let D:=ballHeightParentData (s.fullResample selector).graph center R
  refine ⟨graphBall_connected _ center R,?_⟩
  apply acyclic_of_connected_generators_empty B D
    (D.tree_le _ (ballHeightParentData_parent_adj _ center R))
  intro F hF
  obtain ⟨v⟩:=hF.nonempty
  have hne:F.val≠⊥:=by
    intro hbot
    obtain ⟨w,hw⟩:=(F.val.mem_support).mp v.property
    simp only [hbot,SimpleGraph.bot_adj] at hw
  have ht:ParentCut.terminal D s.graph Subtype.val v.val=D.root:=by
    apply Classical.byContradiction
    intro hnot
    obtain ⟨i,side,_,hc,_,_⟩:=h.terminal_exit center F hF v.val v.property hne hnot
    exact Set.disjoint_left.mp (h.inner_disjoint i) hc hcenter
  apply ParentCut.connected_even_eq_bot_of_terminal_ball_forest D s.graph
    (⟨Subtype.val,Subtype.val_injective⟩:
      graphBallVertices (s.fullResample selector).graph center R↪V)
    R (ballVertexHeight_le _ center R) F.val hF (h.even_parent_old center F)
    (h.even_old_edges center F) F.property.2 v.val v.property
  change (graphBall s.graph (ParentCut.terminal D s.graph Subtype.val v.val).val R).IsAcyclic
  rw [ht]
  exact hOld.IsAcyclic

end LabelledResamplingState
end SpectralConsequences
#print axioms SpectralConsequences.LabelledResamplingState.ProtectedPatches.same_radius_excess
#print axioms SpectralConsequences.LabelledResamplingState.ProtectedPatches.same_radius_root_tree
