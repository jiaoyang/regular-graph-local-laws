import LocalLaw.ShortCycleTreePatch
import LocalLaw.GoodSampleEvenPatterns

/-! # A good sampleward last changed edge cannot lead to a short cycle -/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
namespace LabelledResamplingState

local instance goodSampleCycleBranchesDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V] {T : Set V} {ι : Type*} [Fintype ι]

theorem fullResample_good_sampleward_cycle_impossible (s : LabelledResamplingState V T ι)
    (selector R r : ℕ) (hr : 2 * r ≤ R) (i : ι) (hi : s.Eligible selector i)
    (hmark : s.boundary i ∉ sampledBoundaryHitIndices s.graph T R s.samples)
    (hother : s.boundary i ∉ sampledOtherTripleIndices s.graph T R s.samples)
    (htree : s.boundary i ∉ nonTreeSampledPairIndices s.graph T R s.samples)
    {u v z : V} (hnot : ¬ s.graph.Adj u v)
    (hbranch : (u = (s.quad i).b ∧ v = (s.quad i).c) ∨
      (u = (s.quad i).a ∧ v = (s.quad i).d))
    (suffix : (s.graph ⊓ (s.fullResample selector).graph).Walk v z)
    (hsuffix : suffix.length ≤ r)
    (cycle : (s.fullResample selector).graph.Walk z z) (hcycle : cycle.IsCycle)
    (hcycleLen : cycle.length ≤ 2 * r + 1) : False := by
  let W := pairBallVertices s.graph (s.quad i).c (s.quad i).d R
  have hWtree : (s.graph.induce W).IsTree :=
    sampled_ambient_pair_ball_isTree s.graph T R s.samples (s.boundary i) hmark htree
  have hinside := s.fullResample_good_patch_inside selector R i hi hmark hother
  have hcross := s.fullResample_good_patch_cross selector R i hi hmark hother
  rcases hbranch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · apply short_cycle_not_reached_by_common_walk_from_split_patch s.graph
      (s.fullResample selector).graph W (s.quad i).c (s.quad i).d (s.quad i).b (s.quad i).a
      (Or.inl (by simp)) (Or.inr (by simp))
      (s.samples (s.boundary i)).property.1 hWtree R r hr ?_ hinside hcross
      (fun h => hnot h.symm) cycle hcycle hcycleLen suffix hsuffix
    intro w hw
    exact lt_of_not_ge (fun h => hw (Or.inl h))
  · apply short_cycle_not_reached_by_common_walk_from_split_patch s.graph
      (s.fullResample selector).graph W (s.quad i).d (s.quad i).c (s.quad i).a (s.quad i).b
      (Or.inr (by simp)) (Or.inl (by simp))
      (s.samples (s.boundary i)).property.1.symm hWtree R r hr ?_ ?_ ?_
      (fun h => hnot h.symm) cycle hcycle hcycleLen suffix hsuffix
    · intro w hw
      exact lt_of_not_ge (fun h => hw (Or.inr h))
    · intro a b hab
      rw [SimpleGraph.edge_comm (⟨(s.quad i).d, Or.inr (by simp)⟩ : W)
        (⟨(s.quad i).c, Or.inl (by simp)⟩ : W)]
      exact hinside a b hab
    · intro a ha b hb hab
      have h := hcross a ha b hb hab
      tauto

end LabelledResamplingState
end LocalLaw
