import LocalLaw.IsolatedSwitchNeighborhood

/-!
# Actual edge identities on a good sampled tree patch

Inside the original sample-pair tree, full resampling removes exactly b-c.
Its only new outward edges are b-a and c-l. These pointwise identities are
derived from the actual full schedule and simple-switch formula.
-/

noncomputable section
set_option maxHeartbeats 1200000
namespace LocalLaw

local instance sampleTreePatchDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*}

theorem SwitchingQuad.apply_inside_patch (q : SwitchingQuad V) (G : SimpleGraph V)
    (W : Set V) (ha : q.a ∉ W) (hb : q.b ∉ W) (hc : q.c ∈ W) (hd : q.d ∈ W)
    (u v : W) (h : (q.apply G).Adj u.val v.val) :
    ((G.induce W) \ SimpleGraph.edge (⟨q.c, hc⟩ : W) (⟨q.d, hd⟩ : W)).Adj u v := by
  simp only [SwitchingQuad.apply, simpleSwitch, switchingRemoved, switchingAdded,
    SimpleGraph.sup_adj, SimpleGraph.sdiff_adj] at h
  rcases h with hold | hnew
  · refine ⟨hold.1, ?_⟩
    intro he
    have he' := (SimpleGraph.edge_adj (⟨q.c, hc⟩ : W) (⟨q.d, hd⟩ : W) u v).mp he
    have hraw : (SimpleGraph.edge q.c q.d).Adj u.val v.val := by
      apply (SimpleGraph.edge_adj _ _ _ _).mpr
      refine ⟨?_, hold.1.ne⟩
      rcases he'.1 with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · exact Or.inl ⟨congrArg Subtype.val hu, congrArg Subtype.val hv⟩
      · exact Or.inr ⟨congrArg Subtype.val hu, congrArg Subtype.val hv⟩
    exact hold.2 (Or.inr hraw)
  · rcases hnew with hnew | hnew
    · rcases (SimpleGraph.edge_adj q.a q.d u.val v.val).mp hnew with ⟨hnew, _⟩
      rcases hnew with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · exact False.elim (ha (hu ▸ u.property))
      · exact False.elim (ha (hv ▸ v.property))
    · rcases (SimpleGraph.edge_adj q.b q.c u.val v.val).mp hnew with ⟨hnew, _⟩
      rcases hnew with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · exact False.elim (hb (hu ▸ u.property))
      · exact False.elim (hb (hv ▸ v.property))

theorem SwitchingQuad.apply_cross_patch (q : SwitchingQuad V) (G : SimpleGraph V)
    (W : Set V) (ha : q.a ∉ W) (hb : q.b ∉ W) {u v : V}
    (hu : u ∈ W) (_hv : v ∉ W) (h : (q.apply G).Adj u v) :
    G.Adj u v ∨ (u = q.c ∧ v = q.b) ∨ (u = q.d ∧ v = q.a) := by
  simp only [SwitchingQuad.apply, simpleSwitch, switchingRemoved, switchingAdded,
    SimpleGraph.sup_adj, SimpleGraph.sdiff_adj] at h
  rcases h with hold | hnew
  · exact Or.inl hold.1
  · rcases hnew with hnew | hnew
    · rcases (SimpleGraph.edge_adj q.a q.d u v).mp hnew with ⟨hnew, _⟩
      rcases hnew with ⟨hul, hvc⟩ | ⟨huc, hvl⟩
      · exact False.elim (ha (hul ▸ hu))
      · exact Or.inr (Or.inr ⟨huc, hvl⟩)
    · rcases (SimpleGraph.edge_adj q.b q.c u v).mp hnew with ⟨hnew, _⟩
      rcases hnew with ⟨hua, hvb⟩ | ⟨hub, hva⟩
      · exact False.elim (hb (hua ▸ hu))
      · exact Or.inr (Or.inl ⟨hub, hva⟩)

variable [Fintype V]

theorem sampled_pair_ball_avoids_own_boundary (G : SimpleGraph V) (T : Set V)
    (R : ℕ) (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hmark : α ∉ sampledBoundaryHitIndices G T R S) :
    α.val.2 ∉ pairBallVertices G (S α).val.1 (S α).val.2 R := by
  intro ha
  apply hmark
  apply (mem_endpointHitIndices G T _ S α).mpr
  have hroot : α.val.2 ∈ boundaryExteriorRoots G T := Finset.mem_image.mpr ⟨α, Finset.mem_univ _, rfl⟩
  rcases ha with ha | ha
  · exact Or.inl (Set.mem_toFinset.mpr ⟨α.val.2, hroot, by rwa [SimpleGraph.edist_comm]⟩)
  · exact Or.inr (Set.mem_toFinset.mpr ⟨α.val.2, hroot, by rwa [SimpleGraph.edist_comm]⟩)

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*} [Fintype ι]

theorem fullResample_good_patch_inside (s : LabelledResamplingState V T ι)
    (selector R : ℕ) (i : ι) (hi : s.Eligible selector i)
    (hmark : s.boundary i ∉ sampledBoundaryHitIndices s.graph T R s.samples)
    (hother : s.boundary i ∉ sampledOtherTripleIndices s.graph T R s.samples) :
    let W := pairBallVertices s.graph (s.quad i).c (s.quad i).d R
    ∀ u v : W, (s.fullResample selector).graph.Adj u.val v.val →
      ((s.graph.induce W) \ SimpleGraph.edge (⟨(s.quad i).c, Or.inl (by simp)⟩ : W)
        (⟨(s.quad i).d, Or.inr (by simp)⟩ : W)).Adj u v := by
  dsimp only
  let W := pairBallVertices s.graph (s.quad i).c (s.quad i).d R
  have hout := sampled_ambient_pair_ball_avoids_interior s.graph T R s.samples (s.boundary i) hmark
  have ha : (s.quad i).a ∉ W := fun h => hout _ h (sampledSwitching_root_mem s.graph T s.samples (s.boundary i))
  have hb : (s.quad i).b ∉ W := sampled_pair_ball_avoids_own_boundary s.graph T R s.samples (s.boundary i) hmark
  intro u v h
  apply (s.quad i).apply_inside_patch s.graph W ha hb (Or.inl (by simp)) (Or.inr (by simp))
  exact (s.fullResample_good_sample_neighborhood_incident selector R i hi hmark hother u.property).mp h

theorem fullResample_good_patch_cross (s : LabelledResamplingState V T ι)
    (selector R : ℕ) (i : ι) (hi : s.Eligible selector i)
    (hmark : s.boundary i ∉ sampledBoundaryHitIndices s.graph T R s.samples)
    (hother : s.boundary i ∉ sampledOtherTripleIndices s.graph T R s.samples) :
    ∀ u ∈ pairBallVertices s.graph (s.quad i).c (s.quad i).d R,
      ∀ v ∉ pairBallVertices s.graph (s.quad i).c (s.quad i).d R,
      (s.fullResample selector).graph.Adj u v → s.graph.Adj u v ∨
        (u = (s.quad i).c ∧ v = (s.quad i).b) ∨ (u = (s.quad i).d ∧ v = (s.quad i).a) := by
  let W := pairBallVertices s.graph (s.quad i).c (s.quad i).d R
  have hout := sampled_ambient_pair_ball_avoids_interior s.graph T R s.samples (s.boundary i) hmark
  have ha : (s.quad i).a ∉ W := fun h => hout _ h (sampledSwitching_root_mem s.graph T s.samples (s.boundary i))
  have hb : (s.quad i).b ∉ W := sampled_pair_ball_avoids_own_boundary s.graph T R s.samples (s.boundary i) hmark
  intro u hu v hv h
  apply (s.quad i).apply_cross_patch s.graph W ha hb hu hv
  exact (s.fullResample_good_sample_neighborhood_incident selector R i hi hmark hother hu).mp h

end LabelledResamplingState
end LocalLaw
