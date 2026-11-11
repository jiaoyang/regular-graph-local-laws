import LocalLaw.ShortPatchWalks
import LocalLaw.SampleTreePatch
import LocalLaw.ResamplingLargeIsolation

/-! # Coreward good switching edges visible from an actual ball center

A simple short path approaching either attachment from a good sampled tree
branch lies entirely outside the interior set. Its actual outside distance
places that switching label in the switched nearby-triple set, whose count
has already been proved from the original geometric sampling event.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
namespace LabelledResamplingState

local instance goodSamplePathSeedsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V] {T : Set V} {ι : Type*} [Fintype ι]

theorem fullResample_good_coreward_path_near (s : LabelledResamplingState V T ι)
    (selector R r : ℕ) (hr : r ≤ R) (i : ι) (hi : s.Eligible selector i)
    (hmark : s.boundary i ∉ sampledBoundaryHitIndices s.graph T R s.samples)
    (hother : s.boundary i ∉ sampledOtherTripleIndices s.graph T R s.samples)
    (htree : s.boundary i ∉ nonTreeSampledPairIndices s.graph T R s.samples)
    {center u v : V} (p : (s.fullResample selector).graph.Walk center u)
    (huv : (s.fullResample selector).graph.Adj u v) (hp : (p.concat huv).IsPath)
    (hlen : p.length ≤ r)
    (hcore : (u = (s.quad i).c ∧ v = (s.quad i).b) ∨
      (u = (s.quad i).d ∧ v = (s.quad i).a)) :
    ∃ hx : center ∉ T,
      i ∈ (s.fullResample selector).labelledTripleNearIndices r ⟨center, hx⟩ := by
  classical
  let W := pairBallVertices s.graph (s.quad i).c (s.quad i).d R
  have hWtree : (s.graph.induce W).IsTree :=
    sampled_ambient_pair_ball_isTree s.graph T R s.samples (s.boundary i) hmark htree
  have hinside := s.fullResample_good_patch_inside selector R i hi hmark hother
  have hcross := s.fullResample_good_patch_cross selector R i hi hmark hother
  have hsupport : ∀ w ∈ p.support, w ∈ W := by
    rcases hcore with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · apply short_path_before_patch_entry_support s.graph (s.fullResample selector).graph W
        (s.quad i).c (s.quad i).d (s.quad i).b (s.quad i).a
        (Or.inl (by simp)) (Or.inr (by simp))
        (s.samples (s.boundary i)).property.1 hWtree R ?_ hinside hcross p huv hp (hlen.trans hr)
      intro w hw
      exact lt_of_not_ge (fun h => hw (Or.inl h))
    · apply short_path_before_patch_entry_support s.graph (s.fullResample selector).graph W
        (s.quad i).d (s.quad i).c (s.quad i).a (s.quad i).b
        (Or.inr (by simp)) (Or.inl (by simp))
        (s.samples (s.boundary i)).property.1.symm hWtree R ?_ ?_ ?_ p huv hp (hlen.trans hr)
      · intro w hw
        exact lt_of_not_ge (fun h => hw (Or.inr h))
      · intro a b hab
        rw [SimpleGraph.edge_comm (⟨(s.quad i).d, Or.inr (by simp)⟩ : W)
          (⟨(s.quad i).c, Or.inl (by simp)⟩ : W)]
        exact hinside a b hab
      · intro a ha b hb hab
        have h := hcross a ha b hb hab
        tauto
  have hout : ∀ w ∈ W, w ∉ T :=
    sampled_ambient_pair_ball_avoids_interior s.graph T R s.samples (s.boundary i) hmark
  have hx : center ∉ T := hout center (hsupport center p.start_mem_support)
  have hu : u ∉ T := hout u (hsupport u p.end_mem_support)
  have hsuppOutside : ∀ w ∈ p.reverse.support, w ∈ {w : V | w ∉ T} := by
    intro w hw
    apply hout w
    apply hsupport w
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hw
  obtain ⟨q, hq⟩ := walk_lift_induce_of_support (s.fullResample selector).graph
    {w : V | w ∉ T} p.reverse hu hx hsuppOutside
  refine ⟨hx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  change ∃ y ∈ (s.fullResample selector).triple i,
    (outsideGraph (s.fullResample selector).graph T).edist y ⟨center, hx⟩ ≤ (r : ℕ∞)
  refine ⟨⟨u, hu⟩, ?_, (SimpleGraph.edist_le q).trans ?_⟩
  · rw [s.fullResample_triple selector i]
    rcases hcore with ⟨hu, _⟩ | ⟨hu, _⟩
    · change u ∈ (s.quad i).exterior
      exact hu ▸ Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · change u ∈ (s.quad i).exterior
      exact hu ▸ Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · exact ENat.coe_le_coe.mpr (hq.trans_le (by simpa using hlen))

end LabelledResamplingState
end LocalLaw
