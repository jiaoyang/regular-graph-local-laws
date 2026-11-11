import LocalLaw.PendantTreePatch
import LocalLaw.SampleTreePatch
import LocalLaw.BallEvenGeneratorAvoidance

/-!
# Good sampled tree branches carry no large-ball cyclic pattern

The actual full resampling splits the good ambient sample tree at b-c and
attaches the two pieces separately. The pendant-patch cut proof excludes
both sample roots from every even pattern on at most R+1 vertices. Actual
BFS generation then excludes those roots from every even pattern inside a
radius-R/2 switched ball, regardless of the pattern's size.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
namespace LabelledResamplingState

local instance goodSampleEvenPatternsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V] {T : Set V} {ι : Type*} [Fintype ι]

theorem fullResample_good_sample_short_even_avoids (s : LabelledResamplingState V T ι)
    (selector R : ℕ) (i : ι) (hi : s.Eligible selector i)
    (hmark : s.boundary i ∉ sampledBoundaryHitIndices s.graph T R s.samples)
    (hother : s.boundary i ∉ sampledOtherTripleIndices s.graph T R s.samples)
    (htree : s.boundary i ∉ nonTreeSampledPairIndices s.graph T R s.samples)
    (F : SimpleGraph V) (hFH : F ≤ (s.fullResample selector).graph)
    (heven : ∀ v, Even (F.degree v)) (hsize : F.support.toFinset.card ≤ R + 1) :
    (s.quad i).c ∉ F.support ∧ (s.quad i).d ∉ F.support := by
  let W := pairBallVertices s.graph (s.quad i).c (s.quad i).d R
  have hWtree : (s.graph.induce W).IsTree :=
    sampled_ambient_pair_ball_isTree s.graph T R s.samples (s.boundary i) hmark htree
  have hfarb : ∀ v ∉ W, (R : ℕ∞) < s.graph.edist (s.quad i).c v := by
    intro v hv
    apply lt_of_not_ge
    intro hnear
    exact hv (Or.inl hnear)
  have hfarc : ∀ v ∉ W, (R : ℕ∞) < s.graph.edist (s.quad i).d v := by
    intro v hv
    apply lt_of_not_ge
    intro hnear
    exact hv (Or.inr hnear)
  exact even_pattern_avoids_split_tree_roots s.graph (s.fullResample selector).graph W
    (s.quad i).c (s.quad i).d (s.quad i).b (s.quad i).a (Or.inl (by simp)) (Or.inr (by simp))
    (s.samples (s.boundary i)).property.1 hWtree R hfarb hfarc
    (s.fullResample_good_patch_inside selector R i hi hmark hother)
    (s.fullResample_good_patch_cross selector R i hi hmark hother) F hFH heven hsize

/-- Large-ball conclusion for every even edge pattern, not just for the
particular short generators used in its proof. -/
theorem fullResample_ball_even_avoids_good_sample (s : LabelledResamplingState V T ι)
    (selector R r : ℕ) (hsmall : 2 * r ≤ R) (i : ι) (hi : s.Eligible selector i)
    (hmark : s.boundary i ∉ sampledBoundaryHitIndices s.graph T R s.samples)
    (hother : s.boundary i ∉ sampledOtherTripleIndices s.graph T R s.samples)
    (htree : s.boundary i ∉ nonTreeSampledPairIndices s.graph T R s.samples)
    (center : V) (C : EvenEdgeSubgraph (graphBall (s.fullResample selector).graph center r)) :
    ∀ v : graphBallVertices (s.fullResample selector).graph center r,
      v.val = (s.quad i).c ∨ v.val = (s.quad i).d → v ∉ C.val.support := by
  let A : Set V := {(s.quad i).c, (s.quad i).d}
  apply ball_even_patterns_avoid_of_small_patterns (s.fullResample selector).graph center r A ?_ C
  intro F hF heven hsize
  have hroots := s.fullResample_good_sample_short_even_avoids selector R i hi hmark hother htree
    F hF heven (hsize.trans (by omega))
  intro x hx
  rcases hx with rfl | rfl
  · exact hroots.1
  · exact hroots.2

/-- The source literal radius-R/2 specialization. -/
theorem fullResample_half_ball_even_avoids_good_sample (s : LabelledResamplingState V T ι)
    (selector R : ℕ) (i : ι) (hi : s.Eligible selector i)
    (hmark : s.boundary i ∉ sampledBoundaryHitIndices s.graph T R s.samples)
    (hother : s.boundary i ∉ sampledOtherTripleIndices s.graph T R s.samples)
    (htree : s.boundary i ∉ nonTreeSampledPairIndices s.graph T R s.samples)
    (center : V) (C : EvenEdgeSubgraph (graphBall (s.fullResample selector).graph center (R / 2))) :
    ∀ v : graphBallVertices (s.fullResample selector).graph center (R / 2),
      v.val = (s.quad i).c ∨ v.val = (s.quad i).d → v ∉ C.val.support :=
  s.fullResample_ball_even_avoids_good_sample selector R (R / 2) (by omega) i hi hmark hother htree center C

end LabelledResamplingState
end LocalLaw
