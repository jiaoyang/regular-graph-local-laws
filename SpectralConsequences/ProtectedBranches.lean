import SpectralConsequences.ProtectedSamplePatches
import LocalLaw.ShortPatchWalks

/-! The two sides of each sampled old tree edge are distinct branches.
A center reached from an attachment side determines a unique patch and side. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace SpectralConsequences
open LocalLaw
local instance protectedBranchesDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type*}[Fintype V]{T:Set V}{ι:Type*}[Fintype ι]

def samplePort (s:LocalLaw.LabelledResamplingState V T ι)(i:ι)(side:Bool):V:=
  if side then (s.quad i).d else (s.quad i).c

def sampleAnchor (s:LocalLaw.LabelledResamplingState V T ι)(i:ι)(side:Bool):V:=
  if side then (s.quad i).a else (s.quad i).b

omit [Fintype V] [Fintype ι] in
theorem samplePort_mem (s:LocalLaw.LabelledResamplingState V T ι)(R:ℕ)(i:ι)(side:Bool):
    samplePort s i side∈protectedPatch s R i:=by
  cases side
  · exact Or.inl (center_mem_graphBall _ _ _)
  · exact Or.inr (center_mem_graphBall _ _ _)

def protectedBranchGraph (s:LocalLaw.LabelledResamplingState V T ι)(R:ℕ)(i:ι):
    SimpleGraph (protectedPatch s R i):=
  (s.graph.induce (protectedPatch s R i))\SimpleGraph.edge
    ⟨(s.quad i).c,samplePort_mem s R i false⟩
    ⟨(s.quad i).d,samplePort_mem s R i true⟩

omit [Fintype V] [Fintype ι] in
theorem old_ball_subset_patch (s:LocalLaw.LabelledResamplingState V T ι)
    (R:ℕ)(i:ι)(side:Bool)(x:V)
    (hnear:s.graph.edist (samplePort s i side) x≤(R:ℕ∞)):
    graphBallVertices s.graph x R⊆protectedPatch s R i:=by
  intro y hy
  have hd:s.graph.edist (samplePort s i side) y≤((2*R+1:ℕ):ℕ∞):=
    (s.graph.edist_triangle (u:=samplePort s i side) (v:=x) (w:=y)).trans ((add_le_add hnear hy).trans (by
      rw [←ENat.coe_add]
      exact ENat.coe_le_coe.mpr (by omega)))
  cases side
  · exact Or.inl hd
  · exact Or.inr hd

omit [Fintype V] in
theorem ProtectedPatches.branch_separated (s:LocalLaw.LabelledResamplingState V T ι)
    (selector R:ℕ)(h:ProtectedPatches s selector R)(i:ι):
    ¬(protectedBranchGraph s R i).Reachable
      ⟨(s.quad i).c,samplePort_mem s R i false⟩
      ⟨(s.quad i).d,samplePort_mem s R i true⟩:=by
  have hedge:(s.graph.induce (protectedPatch s R i)).Adj
      ⟨(s.quad i).c,samplePort_mem s R i false⟩
      ⟨(s.quad i).d,samplePort_mem s R i true⟩:=
    (s.samples (s.boundary i)).property.1
  have hb: (s.graph.induce (protectedPatch s R i)).IsBridge
      s((⟨(s.quad i).c,samplePort_mem s R i false⟩:protectedPatch s R i),
        (⟨(s.quad i).d,samplePort_mem s R i true⟩:protectedPatch s R i)):=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp (h.tree i).IsAcyclic) hedge
  exact (SimpleGraph.isBridge_iff.mp hb).2

omit [Fintype V] in
theorem ProtectedPatches.branch_unique (s:LocalLaw.LabelledResamplingState V T ι)
    (selector R:ℕ)(h:ProtectedPatches s selector R)(x:V)(i j:ι)(b c:Bool)
    (hi:x∈protectedPatch s R i)(hj:x∈protectedPatch s R j)
    (pi:(protectedBranchGraph s R i).Reachable
      ⟨samplePort s i b,samplePort_mem s R i b⟩ ⟨x,hi⟩)
    (pj:(protectedBranchGraph s R j).Reachable
      ⟨samplePort s j c,samplePort_mem s R j c⟩ ⟨x,hj⟩):i=j ∧b=c:=by
  have hij:i=j:=by
    by_contra hne
    exact Set.disjoint_left.mp (h.disjoint i j hne) hi hj
  subst j
  refine ⟨rfl,?_⟩
  cases b <;> cases c
  · rfl
  · exact False.elim (h.branch_separated s selector R i (pi.trans pj.symm))
  · exact False.elim (h.branch_separated s selector R i (pj.trans pi.symm))
  · rfl

end LabelledResamplingState
end SpectralConsequences
