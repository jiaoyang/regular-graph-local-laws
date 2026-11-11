import SpectralConsequences.LargePatchSampling

/-! Concrete protected tree-patch data for same-radius switch-exit geometry. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance protectedSamplePatchesDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type*}[Fintype V]{T:Set V}{ι:Type*}[Fintype ι]

def protectedPatch (s:LocalLaw.LabelledResamplingState V T ι)(R:ℕ)(i:ι):Set V:=
  pairBallVertices s.graph (s.quad i).c (s.quad i).d (2*R+1)

structure ProtectedPatches (s:LocalLaw.LabelledResamplingState V T ι)(selector R:ℕ):Prop where
  accepted:∀i,s.Eligible selector i
  tree:∀i,(s.graph.induce (protectedPatch s R i)).IsTree
  inner_disjoint:∀i,Disjoint (protectedPatch s R i) T
  boundary_avoided:∀i j,(s.quad j).b∉protectedPatch s R i
  disjoint:∀i j,i≠j→Disjoint (protectedPatch s R i) (protectedPatch s R j)
  no_old_cross:∀i j,i≠j→∀x∈protectedPatch s R i,∀y∈protectedPatch s R j,¬s.graph.Adj x y
  incident_exact:∀i,∀x∈protectedPatch s R i,∀y,
    (s.fullResample selector).graph.Adj x y↔((s.quad i).apply s.graph).Adj x y

omit [Fintype ι] in
private theorem pair_patch_avoids_boundary (s:LocalLaw.LabelledResamplingState V T ι)
    (M r:ℕ)(hr:r≤M)(hS:AllLargeSampleGood s.graph T M s.samples)(i j:ι):
    (s.quad j).b∉pairBallVertices s.graph (s.quad i).c (s.quad i).d r:=by
  intro hx
  have hmark:s.boundary i∉sampledBoundaryHitIndices s.graph T M s.samples:=by rw [hS.1];simp
  apply hmark
  apply (mem_endpointHitIndices s.graph T _ s.samples (s.boundary i)).mpr
  have hroot:(s.boundary j).val.2∈boundaryExteriorRoots s.graph T:=
    Finset.mem_image.mpr ⟨s.boundary j,Finset.mem_univ _,rfl⟩
  rcases hx with hx|hx
  · exact Or.inl (Set.mem_toFinset.mpr ⟨(s.boundary j).val.2,hroot,
      by rw [SimpleGraph.edist_comm];exact hx.trans (ENat.coe_le_coe.mpr hr)⟩)
  · exact Or.inr (Set.mem_toFinset.mpr ⟨(s.boundary j).val.2,hroot,
      by rw [SimpleGraph.edist_comm];exact hx.trans (ENat.coe_le_coe.mpr hr)⟩)

/-- Every field is derived from actual independent-sample geometry. The
selector remains unchanged; the protective trees may be much larger. -/
theorem protectedPatches_of_allLargeSampleGood (s:LocalLaw.LabelledResamplingState V T ι)
    (selector R M:ℕ)(hM:4*R+3≤M)(hS:AllLargeSampleGood s.graph T M s.samples)
    (hAll:∀i,s.Eligible selector i):ProtectedPatches s selector R:=by
  let r:=2*R+1
  have hr:r≤M:=by dsimp only [r];omega
  have hWT:∀i,Disjoint (protectedPatch s R i) T:=by
    intro i
    apply Set.disjoint_left.mpr
    intro x hx
    apply sampled_ambient_pair_ball_avoids_interior s.graph T M s.samples (s.boundary i)
      (by rw [hS.1];simp) x
    exact hx.imp (fun h=>h.trans (ENat.coe_le_coe.mpr hr)) (fun h=>h.trans (ENat.coe_le_coe.mpr hr))
  have hbound:∀i j,(s.quad j).b∉protectedPatch s R i:=
    pair_patch_avoids_boundary s M r hr hS
  have hsep (i j:ι)(hij:i≠j):
      (M:ℕ∞)<s.graph.edist (s.quad i).c (s.quad j).c ∧
      (M:ℕ∞)<s.graph.edist (s.quad i).c (s.quad j).d ∧
      (M:ℕ∞)<s.graph.edist (s.quad i).d (s.quad j).c ∧
      (M:ℕ∞)<s.graph.edist (s.quad i).d (s.quad j).d:=by
    have hh:=hS.2.1 (s.boundary i) (s.boundary j) (fun h=>hij (s.boundary.injective h))
    simp only [sampledEdgesClose,not_or] at hh
    exact ⟨lt_of_not_ge hh.1.1,lt_of_not_ge hh.1.2,lt_of_not_ge hh.2.1,lt_of_not_ge hh.2.2⟩
  have hdis:∀i j,i≠j→Disjoint (protectedPatch s R i) (protectedPatch s R j):=by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hfar:=hsep i j hij
    have hmono:((2*r:ℕ):ℕ∞)≤(M:ℕ∞):=ENat.coe_le_coe.mpr (by dsimp only [r];omega)
    rcases hx with hx|hx <;> rcases hy with hy|hy
    · exact Set.disjoint_left.mp (graphBalls_disjoint_of_edist_gt s.graph _ _ r (hmono.trans_lt hfar.1)) hx hy
    · exact Set.disjoint_left.mp (graphBalls_disjoint_of_edist_gt s.graph _ _ r (hmono.trans_lt hfar.2.1)) hx hy
    · exact Set.disjoint_left.mp (graphBalls_disjoint_of_edist_gt s.graph _ _ r (hmono.trans_lt hfar.2.2.1)) hx hy
    · exact Set.disjoint_left.mp (graphBalls_disjoint_of_edist_gt s.graph _ _ r (hmono.trans_lt hfar.2.2.2)) hx hy
  refine ⟨hAll,?_,hWT,hbound,hdis,?_,?_⟩
  · intro i
    have hh:=sampled_ambient_pair_ball_isTree s.graph T M s.samples (s.boundary i)
      (by rw [hS.1];simp) (by rw [hS.2.2];simp)
    exact pairBall_isTree_mono s.graph (s.quad i).c (s.quad i).d (s.samples (s.boundary i)).property.1 hr hh
  · intro i j hij x hx y hy
    have hfar:=hsep i j hij
    have hmono:((2*r+1:ℕ):ℕ∞)≤(M:ℕ∞):=ENat.coe_le_coe.mpr (by dsimp only [r];omega)
    rcases hx with hx|hx <;> rcases hy with hy|hy
    · exact graphBalls_no_edge_of_edist_gt s.graph _ _ r (hmono.trans_lt hfar.1) x hx y hy
    · exact graphBalls_no_edge_of_edist_gt s.graph _ _ r (hmono.trans_lt hfar.2.1) x hx y hy
    · exact graphBalls_no_edge_of_edist_gt s.graph _ _ r (hmono.trans_lt hfar.2.2.1) x hx y hy
    · exact graphBalls_no_edge_of_edist_gt s.graph _ _ r (hmono.trans_lt hfar.2.2.2) x hx y hy
  · intro i x hx y
    apply s.fullResample_incident_eq_single selector i (hAll i) (protectedPatch s R i) (hWT i) ?_ hx
    intro j hji
    apply Set.disjoint_left.mpr
    intro v hv hquad
    simp only [SwitchingQuad.exterior,Set.mem_insert_iff,Set.mem_singleton_iff] at hquad
    rcases hquad with h|h|h
    · exact hbound i j (h ▸ hv)
    · exact Set.disjoint_left.mp (hdis i j hji.symm) hv (h ▸ Or.inl (center_mem_graphBall _ _ r))
    · exact Set.disjoint_left.mp (hdis i j hji.symm) hv (h ▸ Or.inr (center_mem_graphBall _ _ r))

end LabelledResamplingState
end SpectralConsequences
#print axioms SpectralConsequences.LabelledResamplingState.protectedPatches_of_allLargeSampleGood
