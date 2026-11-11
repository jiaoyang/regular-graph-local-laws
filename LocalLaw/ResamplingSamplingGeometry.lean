import LocalLaw.BernoulliSampling
import LocalLaw.OutsideEdgeCounting
import LocalLaw.SharpBallCounting

/-!
# Independent geometric endpoint estimates for local resampling

These are genuine finite uniform-sampling bounds: the one-draw probability
is proved from endpoint fibers and the multi-draw tail from independent
function-space sampling. They give the random-endpoint part of (5.20), the
fixed-neighborhood part of (5.21), and bounds for sampling specified bad
centers. Pair-collision counts are not treated as independent events.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw

local instance resamplingSamplingDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The finite uniform-function tail without exposing a measurable-space
choice in a purely finite counting statement. -/
theorem uniform_function_bad_count_power {I E : Type*} [Fintype I] [Fintype E]
    [Nonempty E] (Bad : Finset E) (k : ℕ) :
    eventMass (finiteUniformWeight (I → E))
      (fun f => k ≤ (badSampleIndices Bad f).card) ≤
      ((Fintype.card I : ℝ) * uniformBadProbability Bad) ^ k := by
  letI : MeasurableSpace E := ⊤
  have h := uniform_bad_sample_eventMass_tail (I := I) Bad k
  apply h.trans
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_pow (Fintype.card I) k)
    (pow_nonneg (uniformBadProbability_nonnegative Bad) k)

/-- The finite bad-set fraction is exactly its uniform event mass. -/
theorem uniformBadProbability_eq_eventMass {E : Type*} [Fintype E] (Bad : Finset E) :
    uniformBadProbability Bad = eventMass (finiteUniformWeight E) (fun e => e ∈ Bad) := by
  rw [uniform_eventMass_cardinality]
  have hc : Nat.card {e : E // e ∈ Bad} = Bad.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_of_subtype Bad (by intro e; rfl)
  rw [hc]
  rfl

/-- Outside oriented edges whose first or second endpoint belongs to B. -/
def endpointBadEdges {V : Type*} [Fintype V] (G : SimpleGraph V) (T : Set V)
    (B : Finset V) : Finset (OutsideOrientedEdge G T) :=
  Finset.univ.filter (fun e => e.val.1 ∈ B ∨ e.val.2 ∈ B)

/-- Actual boundary coordinates whose sampled edge hits B. -/
def endpointHitIndices {V : Type*} [Fintype V] (G : SimpleGraph V) (T : Set V)
    (B : Finset V) (S : LocalSamplingFiber G T) : Finset (BoundaryOrientedEdge G T) :=
  badSampleIndices (endpointBadEdges G T B) S

@[simp] theorem mem_endpointHitIndices {V : Type*} [Fintype V] (G : SimpleGraph V)
    (T : Set V) (B : Finset V) (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T) :
    α ∈ endpointHitIndices G T B S ↔ (S α).val.1 ∈ B ∨ (S α).val.2 ∈ B := by
  simp only [endpointHitIndices, badSampleIndices, endpointBadEdges,
    Finset.mem_filter, Finset.mem_univ, true_and]

namespace RegularGraph
variable {N d : ℕ}

/-- A single uniformly sampled outside edge hits B with probability at most
4|B|/N; the outside-edge denominator is derived from |T|≤N/4. -/
theorem endpointBadEdges_probability (g : RegularGraph N d) (T : Set (Fin N))
    (hN : 0 < N) (hd : 0 < d) (hT : 4 * Nat.card T ≤ N) (B : Finset (Fin N)) :
    uniformBadProbability (endpointBadEdges g.graph T B) ≤ 4 * (B.card : ℝ) / N := by
  rw [uniformBadProbability_eq_eventMass]
  have h := g.outside_either_endpoint_probability T hN hd (g.outside_edge_real_size T hT) B
  simpa only [endpointBadEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    outsideEdgeFirst, outsideEdgeSecond] using h

/-- Rare hits of an arbitrary deterministic vertex set under the exact
local-sampling law. No probability bound is part of the hypotheses. -/
theorem localSampling_endpoint_hit_tail (g : RegularGraph N d) (T : Set (Fin N))
    (hN : 0 < N) (hd : 0 < d) (hT : 4 * Nat.card T ≤ N) (B : Finset (Fin N)) (k : ℕ) :
    eventMass (localSamplingWeight g.graph T)
      (fun S => k ≤ (endpointHitIndices g.graph T B S).card) ≤
      ((Nat.card (BoundaryOrientedEdge g.graph T) : ℝ) * (4 * (B.card : ℝ) / N)) ^ k := by
  letI : Nonempty (OutsideOrientedEdge g.graph T) := g.outside_edge_nonempty T hN hd hT
  have hp := g.endpointBadEdges_probability T hN hd hT B
  have h := uniform_function_bad_count_power (I := BoundaryOrientedEdge g.graph T)
    (endpointBadEdges g.graph T B) k
  apply h.trans
  apply pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (uniformBadProbability_nonnegative _))
  simpa only [Nat.card_eq_fintype_card] using
    mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (Fintype.card (BoundaryOrientedEdge g.graph T)))

/-- Fixed-center geometric sampling bound, with the sharp d-1 ball volume. -/
theorem localSampling_near_vertex_tail (g : RegularGraph N d) (T : Set (Fin N))
    (hN : 0 < N) (hd : 3 ≤ d) (hT : 4 * Nat.card T ≤ N) (x : Fin N) (r k : ℕ) :
    eventMass (localSamplingWeight g.graph T)
      (fun S => k ≤ (endpointHitIndices g.graph T
        (graphBallVertices g.graph x r).toFinset S).card) ≤
      ((Nat.card (BoundaryOrientedEdge g.graph T) : ℝ) *
        (4 * (((d + 1) * (d - 1) ^ r : ℕ) : ℝ) / N)) ^ k := by
  apply (g.localSampling_endpoint_hit_tail T hN (by omega) hT _ k).trans
  apply pow_le_pow_left₀ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  exact_mod_cast (by simpa only [Set.toFinset_card, ← Nat.card_eq_fintype_card] using
    graphBall_card_sharp g.graph x d r hd (fun v => (g.regular v).le))

/-- Simultaneous fixed-center estimate. The extra N is the explicit union
over all vertices, not hidden in asymptotic notation. -/
theorem localSampling_any_near_vertex_tail (g : RegularGraph N d) (T : Set (Fin N))
    (hN : 0 < N) (hd : 3 ≤ d) (hT : 4 * Nat.card T ≤ N) (r k : ℕ) :
    eventMass (localSamplingWeight g.graph T)
      (fun S => ∃ x : Fin N, k ≤ (endpointHitIndices g.graph T
        (graphBallVertices g.graph x r).toFinset S).card) ≤
      (N : ℝ) * (((Nat.card (BoundaryOrientedEdge g.graph T) : ℝ) *
        (4 * (((d + 1) * (d - 1) ^ r : ℕ) : ℝ) / N)) ^ k) := by
  have h := eventMass_exists_finset_le (Finset.univ : Finset (Fin N))
    (localSamplingWeight g.graph T) finiteUniformWeight_nonneg
    (fun x S => k ≤ (endpointHitIndices g.graph T
      (graphBallVertices g.graph x r).toFinset S).card)
  simp only [Finset.mem_univ, true_and] at h
  apply h.trans
  calc
    _ ≤ ∑ _x : Fin N, (((Nat.card (BoundaryOrientedEdge g.graph T) : ℝ) *
        (4 * (((d + 1) * (d - 1) ^ r : ℕ) : ℝ) / N)) ^ k) :=
      Finset.sum_le_sum (fun x _ => g.localSampling_near_vertex_tail T hN hd hT x r k)
    _ = _ := by simp

/-- Sampling a specified set of at most b exceptional centers. This is the
independent rare-event input for the tree-neighborhood sampling estimates;
the precise radius needed to certify a two-root tree is kept separate. -/
theorem localSampling_bad_center_tail (g : RegularGraph N d) (T : Set (Fin N))
    (hN : 0 < N) (hd : 0 < d) (hT : 4 * Nat.card T ≤ N)
    (r b k : ℕ) (hbad : (nonTreeCenters g.graph r).card ≤ b) :
    eventMass (localSamplingWeight g.graph T)
      (fun S => k ≤ (endpointHitIndices g.graph T (nonTreeCenters g.graph r) S).card) ≤
      ((Nat.card (BoundaryOrientedEdge g.graph T) : ℝ) * (4 * (b : ℝ) / N)) ^ k := by
  apply (g.localSampling_endpoint_hit_tail T hN hd hT _ k).trans
  apply pow_le_pow_left₀ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hbad) (by norm_num : (0 : ℝ) ≤ 4)

end RegularGraph
end LocalLaw
