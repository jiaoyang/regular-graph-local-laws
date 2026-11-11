import LocalLaw.CollisionMatching

/-!
# The random-endpoint collision estimate for local resampling

The graph on boundary labels joins two distinct coordinates when some of
their sampled endpoints are close. The endpoint occupancy event bounds its
degree. A large active set then contains many disjoint pairs, whose joint
probability was counted in SamplingCollision. This makes the dependency in
the pair-collision part of (5.22) explicit.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw

local instance resamplingCollisionGeometryDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {V : Type*} (G : SimpleGraph V) (T : Set V)

/-- Some endpoint of e is at ambient distance at most r from an endpoint of f. -/
def sampledEdgesClose (r : ℕ) (e f : OutsideOrientedEdge G T) : Prop :=
  (G.edist e.val.1 f.val.1 ≤ (r : ℕ∞) ∨ G.edist e.val.1 f.val.2 ≤ (r : ℕ∞)) ∨
    (G.edist e.val.2 f.val.1 ≤ (r : ℕ∞) ∨ G.edist e.val.2 f.val.2 ≤ (r : ℕ∞))

theorem sampledEdgesClose_symmetric (r : ℕ) : Symmetric (sampledEdgesClose G T r) := by
  intro e f h
  unfold sampledEdgesClose at h ⊢
  rcases h with (h | h) | (h | h)
  · exact Or.inl (Or.inl (by rwa [SimpleGraph.edist_comm]))
  · exact Or.inr (Or.inl (by rwa [SimpleGraph.edist_comm]))
  · exact Or.inl (Or.inr (by rwa [SimpleGraph.edist_comm]))
  · exact Or.inr (Or.inr (by rwa [SimpleGraph.edist_comm]))

theorem sampledEdgesClose_iff_endpoint_hit (r : ℕ) (e f : OutsideOrientedEdge G T) :
    sampledEdgesClose G T r e f ↔
      f.val.1 ∈ pairBallVertices G e.val.1 e.val.2 r ∨
        f.val.2 ∈ pairBallVertices G e.val.1 e.val.2 r := by
  simp only [sampledEdgesClose, pairBallVertices, Set.mem_setOf_eq]
  tauto

variable [Fintype V]

def sampledEdgeCollisionGraph (r : ℕ) (S : LocalSamplingFiber G T) :
    SimpleGraph (BoundaryOrientedEdge G T) :=
  sampleCollisionGraph (sampledEdgesClose G T r) (sampledEdgesClose_symmetric G T r) S

/-- A pointwise occupancy bound at every vertex bounds the collision graph
degree by 2k, because each sampled edge has only two endpoints. -/
theorem sampledEdgeCollisionGraph_degree (r k : ℕ) (S : LocalSamplingFiber G T)
    (hoccupancy : ∀ x, (endpointHitIndices G T (graphBallVertices G x r).toFinset S).card ≤ k)
    (α : BoundaryOrientedEdge G T) : (sampledEdgeCollisionGraph G T r S).degree α ≤ 2 * k := by
  let H := sampledEdgeCollisionGraph G T r S
  have hsub : H.neighborFinset α ⊆
      endpointHitIndices G T (graphBallVertices G (S α).val.1 r).toFinset S ∪
        endpointHitIndices G T (graphBallVertices G (S α).val.2 r).toFinset S := by
    intro β hβ
    have hrel := ((H.mem_neighborFinset α β).mp hβ).2
    change sampledEdgesClose G T r (S α) (S β) at hrel
    simp only [sampledEdgesClose] at hrel
    simpa only [Finset.mem_union, mem_endpointHitIndices, Set.mem_toFinset,
      graphBallVertices, Set.mem_setOf_eq] using hrel
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (by have h₁ := hoccupancy (S α).val.1; have h₂ := hoccupancy (S α).val.2; omega))

namespace RegularGraph
variable {N d : ℕ}

/-- A related-edge fiber has at most 4d times the sharp radius-r ball volume
many choices. This is a count of actual oriented outside edges. -/
theorem sampledEdgesClose_fiber_card (g : RegularGraph N d) (T : Set (Fin N))
    (r : ℕ) (hd : 3 ≤ d) (e : OutsideOrientedEdge g.graph T) :
    Nat.card {f : OutsideOrientedEdge g.graph T // sampledEdgesClose g.graph T r e f} ≤
      4 * d * ((d + 1) * (d - 1) ^ r) := by
  let B := (pairBallVertices g.graph e.val.1 e.val.2 r).toFinset
  have hB : B.card ≤ 2 * ((d + 1) * (d - 1) ^ r) := by
    have heq : B = (graphBallVertices g.graph e.val.1 r).toFinset ∪
        (graphBallVertices g.graph e.val.2 r).toFinset := by
      ext v
      simp only [B, Set.mem_toFinset, Finset.mem_union, pairBallVertices,
        graphBallVertices, Set.mem_setOf_eq]
    rw [heq]
    have h₁ : (graphBallVertices g.graph e.val.1 r).toFinset.card ≤ (d + 1) * (d - 1) ^ r := by
      simpa only [Set.toFinset_card, ← Nat.card_eq_fintype_card] using
        graphBall_card_sharp g.graph e.val.1 d r hd (fun v => (g.regular v).le)
    have h₂ : (graphBallVertices g.graph e.val.2 r).toFinset.card ≤ (d + 1) * (d - 1) ^ r := by
      simpa only [Set.toFinset_card, ← Nat.card_eq_fintype_card] using
        graphBall_card_sharp g.graph e.val.2 d r hd (fun v => (g.regular v).le)
    exact (Finset.card_union_le _ _).trans (by omega)
  let First : Finset (OutsideOrientedEdge g.graph T) := Finset.univ.filter (fun f => f.val.1 ∈ B)
  let Second : Finset (OutsideOrientedEdge g.graph T) := Finset.univ.filter (fun f => f.val.2 ∈ B)
  have hfirst : First.card ≤ B.card * d := by
    have h := endpoint_preimage_card_bound (outsideEdgeFirst g.graph T) B d (fun v =>
      (outsideEdgeFirst_fiber_card g.graph T v).trans_eq (g.regular v))
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, outsideEdgeFirst, First] using h
  have hsecond : Second.card ≤ B.card * d := by
    have h := endpoint_preimage_card_bound (outsideEdgeSecond g.graph T) B d (fun v =>
      (outsideEdgeSecond_fiber_card g.graph T v).trans_eq (g.regular v))
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, outsideEdgeSecond, Second] using h
  have heq : Nat.card {f : OutsideOrientedEdge g.graph T // sampledEdgesClose g.graph T r e f} =
      (First ∪ Second).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext f
    simp only [First, Second, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      sampledEdgesClose_iff_endpoint_hit, B, Set.mem_toFinset]
  rw [heq]
  calc
    _ ≤ First.card + Second.card := Finset.card_union_le _ _
    _ ≤ B.card * d + B.card * d := Nat.add_le_add hfirst hsecond
    _ ≤ (2 * ((d + 1) * (d - 1) ^ r)) * d + (2 * ((d + 1) * (d - 1) ^ r)) * d :=
      Nat.add_le_add (Nat.mul_le_mul_right d hB) (Nat.mul_le_mul_right d hB)
    _ = _ := by ring

/-- The full random--random collision tail, under the original finite local
sampling law. Both the occupancy failure and the dependent pair-event cost
are proved, with every finite-N factor visible. -/
theorem localSampling_many_sampled_edge_collisions (g : RegularGraph N d) (T : Set (Fin N))
    (hN : 0 < N) (hd : 3 ≤ d) (hT : 4 * Nat.card T ≤ N) (r k q : ℕ) :
    eventMass (localSamplingWeight g.graph T) (fun S =>
      2 * q * (2 * k + 1) ≤ (sampledEdgeCollisionGraph g.graph T r S).support.toFinset.card) ≤
      (N : ℝ) * (((Nat.card (BoundaryOrientedEdge g.graph T) : ℝ) *
        (4 * (((d + 1) * (d - 1) ^ r : ℕ) : ℝ) / N)) ^ (k + 1)) +
      ((((Nat.card (BoundaryOrientedEdge g.graph T) : ℝ) ^ 2) *
        (8 * (((d + 1) * (d - 1) ^ r : ℕ) : ℝ) / N)) ^ q) := by
  letI : Nonempty (OutsideOrientedEdge g.graph T) := g.outside_edge_nonempty T hN (by omega) hT
  let R := sampledEdgesClose g.graph T r
  let hR := sampledEdgesClose_symmetric g.graph T r
  let b := 4 * d * ((d + 1) * (d - 1) ^ r)
  let fail : LocalSamplingFiber g.graph T → Prop := fun S => ∃ x : Fin N,
    k + 1 ≤ (endpointHitIndices g.graph T (graphBallVertices g.graph x r).toFinset S).card
  let bounded : LocalSamplingFiber g.graph T → Prop := fun S =>
    (∀ i, (sampleCollisionGraph R hR S).degree i ≤ 2 * k) ∧
      2 * q * (2 * k + 1) ≤ (sampleCollisionGraph R hR S).support.toFinset.card
  have hcover : ∀ S, 2 * q * (2 * k + 1) ≤
      (sampledEdgeCollisionGraph g.graph T r S).support.toFinset.card → fail S ∨ bounded S := by
    intro S hS
    by_cases hf : fail S
    · exact Or.inl hf
    · refine Or.inr ⟨?_, hS⟩
      intro i
      apply sampledEdgeCollisionGraph_degree
      intro x
      have hnot := not_exists.mp hf x
      omega
  have hmass := (eventMass_mono (localSamplingWeight g.graph T) finiteUniformWeight_nonneg hcover).trans
    (eventMass_union_le (localSamplingWeight g.graph T) finiteUniformWeight_nonneg fail bounded)
  have hfail := g.localSampling_any_near_vertex_tail T hN hd hT r (k + 1)
  have hbounded := uniform_collision_support_tail_on_degree
    (I := BoundaryOrientedEdge g.graph T) R hR b (2 * k) q
    (fun e => g.sampledEdgesClose_fiber_card T r hd e)
  have hdenom : (b : ℝ) / Fintype.card (OutsideOrientedEdge g.graph T) ≤
      8 * (((d + 1) * (d - 1) ^ r : ℕ) : ℝ) / N := by
    have hsize := g.outside_edge_real_size T hT
    have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hdp : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
    have hEp : (0 : ℝ) < Fintype.card (OutsideOrientedEdge g.graph T) :=
      Nat.cast_pos.mpr Fintype.card_pos
    apply (div_le_div_iff₀ hEp hNp).mpr
    have hh := mul_le_mul_of_nonneg_right hsize
      (by positivity : (0 : ℝ) ≤ 8 * (((d + 1) * (d - 1) ^ r : ℕ) : ℝ))
    dsimp [b]
    push_cast at hh ⊢
    nlinarith
  apply hmass.trans
  apply add_le_add hfail
  apply hbounded.trans
  apply pow_le_pow_left₀ (by positivity)
  simpa only [Nat.card_eq_fintype_card] using
    mul_le_mul_of_nonneg_left hdenom (sq_nonneg (Fintype.card (BoundaryOrientedEdge g.graph T) : ℝ))

end RegularGraph
end LocalLaw
