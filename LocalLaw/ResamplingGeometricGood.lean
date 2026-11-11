import LocalLaw.ResamplingCollisionGeometry
import LocalLaw.ResamplingTreeSampling
import LocalLaw.BoundaryNearCounts
import LocalLaw.ResamplingSchedule

/-!
# The elementary geometric good-sampling inputs

The deterministic boundary-label count and the independent random-endpoint
count combine to give the triple occupancy in (5.30). A separate fixed-set
estimate controls sampled endpoints near any boundary endpoint. The latter
is one ingredient in the exceptional-index counts in (5.31).
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw

local instance resamplingGeometricGoodDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {V : Type*} [Fintype V]

def boundaryExteriorRoots (G : SimpleGraph V) (T : Set V) : Finset V :=
  Finset.univ.image (fun e : BoundaryOrientedEdge G T => e.val.2)

theorem boundaryExteriorRoots_card (G : SimpleGraph V) (T : Set V) :
    (boundaryExteriorRoots G T).card ≤ Nat.card (BoundaryOrientedEdge G T) := by
  simpa only [Nat.card_eq_fintype_card, Finset.card_univ] using
    (Finset.card_image_le (s := Finset.univ) (f := fun e : BoundaryOrientedEdge G T => e.val.2))

/-- A sample is marked if either endpoint lies in the union of ambient
radius-R balls about all actual outside boundary endpoints. -/
def sampledBoundaryHitIndices (G : SimpleGraph V) (T : Set V) (R : ℕ)
    (S : LocalSamplingFiber G T) : Finset (BoundaryOrientedEdge G T) :=
  endpointHitIndices G T (graphSetBall G (boundaryExteriorRoots G T) R).toFinset S

omit [Fintype V] in
theorem outsideTriple_mem_iff (G : SimpleGraph V) (T : Set V) (S : LocalSamplingFiber G T)
    (α : BoundaryOrientedEdge G T) (x : {v : V // v ∉ T}) :
    x ∈ outsideTriple G T S α ↔ x = boundaryOuterEndpoint G T α ∨
      x = sampledFirstOutsideVertex G T S α ∨ x = sampledSecondOutsideVertex G T S α := by
  simp only [outsideTriple, sampledSwitchingQuad, SwitchingQuad.exterior,
    Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    boundaryOuterEndpoint, sampledFirstOutsideVertex, sampledSecondOutsideVertex,
    Subtype.ext_iff]

/-- Actual triple-nearby coordinates in the deleted graph. -/
def tripleNearIndices (G : SimpleGraph V) (T : Set V) (h : ℕ)
    (S : LocalSamplingFiber G T) (x : {v : V // v ∉ T}) : Finset (BoundaryOrientedEdge G T) :=
  Finset.univ.filter (fun α => ∃ y ∈ outsideTriple G T S α,
    (outsideGraph G T).edist x y ≤ (h : ℕ∞))

/-- The pointwise triple count follows from the proved boundary geometry
and a literal endpoint occupancy count. No graph-distance conclusion is a
field of an assumed sampling certificate. -/
theorem tripleNearIndices_card (G : SimpleGraph V) (o : V) (ell R h ω k : ℕ)
    (hmargin : ell + 1 + h ≤ R) (hbudget : graphBallExcess G o R ≤ ω)
    (S : LocalSamplingFiber G (graphBallVertices G o ell))
    (hoccupancy : ∀ x, (endpointHitIndices G (graphBallVertices G o ell)
      (graphBallVertices G x h).toFinset S).card ≤ k)
    (x : {v : V // v ∉ graphBallVertices G o ell}) :
    (tripleNearIndices G (graphBallVertices G o ell) h S x).card ≤ ω + 1 + k := by
  let T := graphBallVertices G o ell
  have hsub : tripleNearIndices G T h S x ⊆ nearbyBoundaryIndices G o ell h x ∪
      endpointHitIndices G T (graphBallVertices G x.val h).toFinset S := by
    intro α hα
    obtain ⟨y, hy, hdist⟩ := (Finset.mem_filter.mp hα).2
    rcases (outsideTriple_mem_iff G T S α y).mp hy with rfl | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩)
    · apply Finset.mem_union_right
      apply (mem_endpointHitIndices G T _ S α).mpr
      apply Or.inl
      apply Set.mem_toFinset.mpr
      exact (ambient_edist_le_induced_edist G {v | v ∉ T} x
        (sampledFirstOutsideVertex G T S α)).trans hdist
    · apply Finset.mem_union_right
      apply (mem_endpointHitIndices G T _ S α).mpr
      apply Or.inr
      apply Set.mem_toFinset.mpr
      exact (ambient_edist_le_induced_edist G {v | v ∉ T} x
        (sampledSecondOutsideVertex G T S α)).trans hdist
  have hb := nearby_boundary_count G o ell R h ω hmargin hbudget x
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add hb (hoccupancy x.val)))

/-- A deleted-graph path from an outside boundary endpoint puts its other
endpoint in the deterministic ambient union of boundary-root balls. -/
theorem boundary_near_mem_boundary_root_ball (G : SimpleGraph V) (T : Set V)
    (R : ℕ) (e : BoundaryOrientedEdge G T) (x : {v : V // v ∉ T})
    (hnear : (outsideGraph G T).edist (boundaryOuterEndpoint G T e) x ≤ (R : ℕ∞)) :
    x.val ∈ graphSetBall G (boundaryExteriorRoots G T) R := by
  refine ⟨e.val.2, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
  · exact (ambient_edist_le_induced_edist G {v | v ∉ T}
      (boundaryOuterEndpoint G T e) x).trans hnear

/-- Boundary endpoint a_alpha is close to a different coordinate's triple. -/
def boundaryOtherTripleIndices (G : SimpleGraph V) (T : Set V) (h : ℕ)
    (S : LocalSamplingFiber G T) : Finset (BoundaryOrientedEdge G T) :=
  Finset.univ.filter (fun α => ∃ β : BoundaryOrientedEdge G T, β ≠ α ∧
    ∃ y ∈ outsideTriple G T S β,
      (outsideGraph G T).edist (boundaryOuterEndpoint G T α) y ≤ (h : ℕ∞))

/-- A sampled endpoint b_alpha or c_alpha is close to another triple. -/
def sampledOtherTripleIndices (G : SimpleGraph V) (T : Set V) (R : ℕ)
    (S : LocalSamplingFiber G T) : Finset (BoundaryOrientedEdge G T) :=
  Finset.univ.filter (fun α => ∃ β : BoundaryOrientedEdge G T, β ≠ α ∧
    ∃ y ∈ outsideTriple G T S β,
      ((outsideGraph G T).edist (sampledFirstOutsideVertex G T S α) y ≤ (R : ℕ∞) ∨
        (outsideGraph G T).edist (sampledSecondOutsideVertex G T S α) y ≤ (R : ℕ∞)))

/-- The first exceptional-index count in (5.31). Boundary--boundary
collisions use cutset excess; the two endpoint fibers of each marked random
sample use the actual fixed-center boundary count. -/
theorem boundaryOtherTripleIndices_card (G : SimpleGraph V) (o : V) (ell R h ω : ℕ)
    (hmargin : ell + 1 + h ≤ R) (hbudget : graphBallExcess G o R ≤ ω)
    (S : LocalSamplingFiber G (graphBallVertices G o ell)) :
    (boundaryOtherTripleIndices G (graphBallVertices G o ell) h S).card ≤
      2 * ω + (sampledBoundaryHitIndices G (graphBallVertices G o ell) h S).card * (2 * (ω + 1)) := by
  let T := graphBallVertices G o ell
  let B := sampledBoundaryHitIndices G T h S
  let F := fun β : BoundaryOrientedEdge G T =>
    nearbyBoundaryIndices G o ell h (sampledFirstOutsideVertex G T S β) ∪
      nearbyBoundaryIndices G o ell h (sampledSecondOutsideVertex G T S β)
  have hsub : boundaryOtherTripleIndices G T h S ⊆ boundaryCollisionIndices G o ell h ∪ B.biUnion F := by
    intro α hα
    obtain ⟨β, hβα, y, hy, hdist⟩ := (Finset.mem_filter.mp hα).2
    rcases (outsideTriple_mem_iff G T S β y).mp hy with rfl | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, β, hβα, hdist⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨β, ?_, Finset.mem_union_left _ ?_⟩
      · apply (mem_endpointHitIndices G T _ S β).mpr
        exact Or.inl (Set.mem_toFinset.mpr (boundary_near_mem_boundary_root_ball G T h α _ hdist))
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rwa [SimpleGraph.edist_comm]⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨β, ?_, Finset.mem_union_right _ ?_⟩
      · apply (mem_endpointHitIndices G T _ S β).mpr
        exact Or.inr (Set.mem_toFinset.mpr (boundary_near_mem_boundary_root_ball G T h α _ hdist))
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rwa [SimpleGraph.edist_comm]⟩
  have hF : ∀ β, (F β).card ≤ 2 * (ω + 1) := by
    intro β
    have h₁ := nearby_boundary_count G o ell R h ω hmargin hbudget (sampledFirstOutsideVertex G T S β)
    have h₂ := nearby_boundary_count G o ell R h ω hmargin hbudget (sampledSecondOutsideVertex G T S β)
    exact (Finset.card_union_le _ _).trans (by omega)
  have hB : (B.biUnion F).card ≤ B.card * (2 * (ω + 1)) := by
    calc
      _ ≤ ∑ β ∈ B, (F β).card := Finset.card_biUnion_le
      _ ≤ ∑ _β ∈ B, 2 * (ω + 1) := Finset.sum_le_sum (fun β _ => hF β)
      _ = _ := by simp
  have hdet := boundary_collision_count G o ell R h ω hmargin hbudget
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add hdet hB))

/-- The second exceptional-index count in (5.31). Each marked coordinate is
either sampled near a deterministic boundary endpoint, or is an actual
nonisolated vertex of the random--random collision graph. -/
theorem sampledOtherTripleIndices_subset (G : SimpleGraph V) (T : Set V) (R : ℕ)
    (S : LocalSamplingFiber G T) :
    sampledOtherTripleIndices G T R S ⊆ sampledBoundaryHitIndices G T R S ∪
      (sampledEdgeCollisionGraph G T R S).support.toFinset := by
  intro α hα
  obtain ⟨β, hβα, y, hy, hdist⟩ := (Finset.mem_filter.mp hα).2
  rcases (outsideTriple_mem_iff G T S β y).mp hy with rfl | rfl | rfl
  · apply Finset.mem_union_left
    apply (mem_endpointHitIndices G T _ S α).mpr
    rcases hdist with hdist | hdist
    · apply Or.inl
      apply Set.mem_toFinset.mpr
      apply boundary_near_mem_boundary_root_ball G T R β (sampledFirstOutsideVertex G T S α)
      rwa [SimpleGraph.edist_comm]
    · apply Or.inr
      apply Set.mem_toFinset.mpr
      apply boundary_near_mem_boundary_root_ball G T R β (sampledSecondOutsideVertex G T S α)
      rwa [SimpleGraph.edist_comm]
  · apply Finset.mem_union_right
    apply Set.mem_toFinset.mpr
    apply ((sampledEdgeCollisionGraph G T R S).mem_support).mpr
    refine ⟨β, hβα.symm, ?_⟩
    rcases hdist with hd | hd
    · exact Or.inl (Or.inl ((ambient_edist_le_induced_edist G {v | v ∉ T} _ _).trans hd))
    · exact Or.inr (Or.inl ((ambient_edist_le_induced_edist G {v | v ∉ T} _ _).trans hd))
  · apply Finset.mem_union_right
    apply Set.mem_toFinset.mpr
    apply ((sampledEdgeCollisionGraph G T R S).mem_support).mpr
    refine ⟨β, hβα.symm, ?_⟩
    rcases hdist with hd | hd
    · exact Or.inl (Or.inr ((ambient_edist_le_induced_edist G {v | v ∉ T} _ _).trans hd))
    · exact Or.inr (Or.inr ((ambient_edist_le_induced_edist G {v | v ∉ T} _ _).trans hd))

theorem sampledOtherTripleIndices_card (G : SimpleGraph V) (T : Set V) (R : ℕ)
    (S : LocalSamplingFiber G T) :
    (sampledOtherTripleIndices G T R S).card ≤ (sampledBoundaryHitIndices G T R S).card +
      (sampledEdgeCollisionGraph G T R S).support.toFinset.card :=
  (Finset.card_le_card (sampledOtherTripleIndices_subset G T R S)).trans (Finset.card_union_le _ _)

namespace RegularGraph
variable {N d : ℕ}

/-- Independent sampling near the entire deterministic boundary. The extra
factor mu comes from the union of boundary-root neighborhoods. -/
theorem localSampling_boundary_neighborhood_tail (g : RegularGraph N d) (T : Set (Fin N))
    (hN : 0 < N) (hd : 3 ≤ d) (hT : 4 * Nat.card T ≤ N) (R j : ℕ) :
    eventMass (localSamplingWeight g.graph T)
      (fun S => j ≤ (sampledBoundaryHitIndices g.graph T R S).card) ≤
      (4 * (Nat.card (BoundaryOrientedEdge g.graph T) : ℝ) ^ 2 *
        (((d + 1) * (d - 1) ^ R : ℕ) : ℝ) / N) ^ j := by
  let B := (graphSetBall g.graph (boundaryExteriorRoots g.graph T) R).toFinset
  have hroots : Nat.card (boundaryExteriorRoots g.graph T : Set (Fin N)) ≤
      Nat.card (BoundaryOrientedEdge g.graph T) := by
    have heq : Nat.card (boundaryExteriorRoots g.graph T : Set (Fin N)) =
        (boundaryExteriorRoots g.graph T).card := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_of_subtype _ (by intro x; rfl)
    rw [heq]
    exact boundaryExteriorRoots_card g.graph T
  have hB : B.card ≤ Nat.card (BoundaryOrientedEdge g.graph T) * ((d + 1) * (d - 1) ^ R) := by
    have h := graphSetBall_card_sharp g.graph (boundaryExteriorRoots g.graph T) d R hd
      (fun v => (g.regular v).le)
    apply (show B.card ≤ Nat.card (boundaryExteriorRoots g.graph T : Set (Fin N)) *
      ((d + 1) * (d - 1) ^ R) by
      simpa only [B, Set.toFinset_card, ← Nat.card_eq_fintype_card] using h).trans
    exact Nat.mul_le_mul_right _ hroots
  apply (g.localSampling_endpoint_hit_tail T hN (by omega) hT B j).trans
  apply pow_le_pow_left₀ (by positivity)
  have hBr : (B.card : ℝ) ≤ (Nat.card (BoundaryOrientedEdge g.graph T) : ℝ) *
      (((d + 1) * (d - 1) ^ R : ℕ) : ℝ) := by exact_mod_cast hB
  have hh := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hBr (by norm_num : (0 : ℝ) ≤ 4)) (Nat.cast_nonneg N))
    (Nat.cast_nonneg (Nat.card (BoundaryOrientedEdge g.graph T)))
  convert hh using 1
  ring

/-- The source triple-occupancy estimate, with an explicit N-fold union
budget and the actual deleted-graph metric. -/
theorem localSampling_any_triple_occupancy_tail (g : RegularGraph N d) (o : Fin N)
    (ell R h ω k : ℕ) (hN : 0 < N) (hd : 3 ≤ d)
    (hT : 4 * Nat.card (graphBallVertices g.graph o ell) ≤ N)
    (hmargin : ell + 1 + h ≤ R) (hbudget : graphBallExcess g.graph o R ≤ ω) :
    eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o ell)) (fun S =>
      ∃ x : {v : Fin N // v ∉ graphBallVertices g.graph o ell},
        ω + 1 + k + 1 ≤ (tripleNearIndices g.graph (graphBallVertices g.graph o ell) h S x).card) ≤
      (N : ℝ) * (((Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) *
        (4 * (((d + 1) * (d - 1) ^ h : ℕ) : ℝ) / N)) ^ (k + 1)) := by
  apply (eventMass_mono _ finiteUniformWeight_nonneg ?_).trans
    (g.localSampling_any_near_vertex_tail _ hN hd hT h (k + 1))
  intro S hS
  by_contra hnone
  have hoccupancy : ∀ x, (endpointHitIndices g.graph (graphBallVertices g.graph o ell)
      (graphBallVertices g.graph x h).toFinset S).card ≤ k := by
    intro x
    have hx := not_exists.mp hnone x
    omega
  obtain ⟨x, hx⟩ := hS
  have hbound := tripleNearIndices_card g.graph o ell R h ω k hmargin hbudget S hoccupancy x
  omega

end RegularGraph
end LocalLaw
