import SpectralConsequences.ProtectedBranches
import SpectralConsequences.ProtectedPatchEdges

/-! A common two-port interface for the literal before-attachment path lemmas. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace SpectralConsequences
open LocalLaw
local instance protectedPortPathsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type*}[Fintype V]{T:Set V}{ι:Type*}[Fintype ι]
variable {s:LocalLaw.LabelledResamplingState V T ι}{selector R:ℕ}

omit [Fintype V] in
theorem ProtectedPatches.path_before_port (h:ProtectedPatches s selector R)(i:ι)(side:Bool)
    {center:V}(p:(s.fullResample selector).graph.Walk center (samplePort s i side))
    (hentry:(s.fullResample selector).graph.Adj (samplePort s i side) (sampleAnchor s i side))
    (hp:(p.concat hentry).IsPath)(hlen:p.length≤R):
    ∃hc:center∈protectedPatch s R i,∃q:(protectedBranchGraph s R i).Walk
      ⟨samplePort s i side,samplePort_mem s R i side⟩ ⟨center,hc⟩,q.length≤R:=by
  cases side
  · obtain ⟨hc,q,hq⟩:=h.first_path_before_entry i p hentry hp (by omega)
    exact ⟨hc,q,hq.le.trans hlen⟩
  · obtain ⟨hc,q,hq⟩:=h.second_path_before_entry i p hentry hp (by omega)
    have hGraph:((s.graph.induce (protectedPatch s R i))\SimpleGraph.edge
      (⟨(s.quad i).d,Or.inr (center_mem_graphBall _ _ _)⟩:protectedPatch s R i)
      (⟨(s.quad i).c,Or.inl (center_mem_graphBall _ _ _)⟩:protectedPatch s R i))=
        protectedBranchGraph s R i:=by
      rw [SimpleGraph.edge_comm]
      rfl
    refine ⟨hc,q.mapLe (le_of_eq hGraph),?_⟩
    simpa only [SimpleGraph.Walk.length_map] using hq.le.trans hlen

omit [Fintype V] [Fintype ι] in
theorem protectedBranch_distance (s:LocalLaw.LabelledResamplingState V T ι)(R:ℕ)(i:ι)
    (side:Bool)(center:V)(hc:center∈protectedPatch s R i)
    (q:(protectedBranchGraph s R i).Walk
      ⟨samplePort s i side,samplePort_mem s R i side⟩ ⟨center,hc⟩)(hlen:q.length≤R):
    s.graph.edist (samplePort s i side) center≤(R:ℕ∞):=by
  let f:protectedBranchGraph s R i→g s.graph:=
    {toFun:=Subtype.val,map_rel':=fun h=>h.1}
  exact (s.graph.edist_le (q.map f)).trans (by
    simpa only [SimpleGraph.Walk.length_map] using ENat.coe_le_coe.mpr hlen)

end LabelledResamplingState
end SpectralConsequences
