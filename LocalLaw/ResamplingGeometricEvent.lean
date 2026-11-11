import LocalLaw.ResamplingGeometricGood

/-!
# An actual high-probability geometric sampling event

The event contains the three source-(5.31) exceptional-index bounds and the
source-(5.30) occupancy bound. Its finite failure budget is proved from the
uniform sampling law. The switched-graph small/large ball excess conclusions
of Proposition 5.12 are not assumed or asserted by this event construction.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw

local instance resamplingGeometricEventDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {V : Type*} [Fintype V]

theorem endpointHitIndices_mono (G : SimpleGraph V) (T : Set V)
    (B C : Finset V) (hBC : B ⊆ C) (S : LocalSamplingFiber G T) :
    endpointHitIndices G T B S ⊆ endpointHitIndices G T C S := by
  intro α hα
  rw [mem_endpointHitIndices] at hα ⊢
  exact hα.imp (fun h => hBC h) (fun h => hBC h)

theorem sampledBoundaryHitIndices_mono (G : SimpleGraph V) (T : Set V)
    {r R : ℕ} (hr : r ≤ R) (S : LocalSamplingFiber G T) :
    sampledBoundaryHitIndices G T r S ⊆ sampledBoundaryHitIndices G T R S := by
  apply endpointHitIndices_mono
  intro x hx
  obtain ⟨a, ha, hd⟩ := Set.mem_toFinset.mp hx
  exact Set.mem_toFinset.mpr ⟨a, ha, hd.trans (ENat.coe_le_coe.mpr hr)⟩

/-- Literal source geometric conclusions at integer radii, with explicit
constants determined by the finite counting parameters. -/
def SourceGeometricGood (G : SimpleGraph V) (o : V) (ell R ω k j C t : ℕ)
    (S : LocalSamplingFiber G (graphBallVertices G o ell)) : Prop :=
  (∀ x : {v : V // v ∉ graphBallVertices G o ell},
    (tripleNearIndices G (graphBallVertices G o ell) (R / 2) S x).card ≤ ω + 1 + k) ∧
  (boundaryOtherTripleIndices G (graphBallVertices G o ell) (R / 2) S).card ≤
    2 * ω + j * (2 * (ω + 1)) ∧
  (sampledOtherTripleIndices G (graphBallVertices G o ell) R S).card ≤ j + C ∧
  (nonTreeSampledPairIndices G (graphBallVertices G o ell) R S).card ≤ t

theorem sourceGeometricGood_of_counts (G : SimpleGraph V) (o : V) (ell R ω k j C t : ℕ)
    (hmargin : 2 * ell + 2 ≤ R) (hbudget : graphBallExcess G o R ≤ ω)
    (S : LocalSamplingFiber G (graphBallVertices G o ell))
    (hoccupancy : ∀ x, (endpointHitIndices G (graphBallVertices G o ell)
      (graphBallVertices G x R).toFinset S).card ≤ k)
    (hdet : (sampledBoundaryHitIndices G (graphBallVertices G o ell) R S).card ≤ j)
    (hrandom : (sampledEdgeCollisionGraph G (graphBallVertices G o ell) R S).support.toFinset.card ≤ C)
    (hpair : (nonTreeSampledPairIndices G (graphBallVertices G o ell) R S).card ≤ t) :
    SourceGeometricGood G o ell R ω k j C t S := by
  have hhalf : R / 2 ≤ R := Nat.div_le_self _ _
  have hfit : ell + 1 + R / 2 ≤ R := by omega
  have hdetHalf : (sampledBoundaryHitIndices G (graphBallVertices G o ell) (R / 2) S).card ≤ j :=
    (Finset.card_le_card (sampledBoundaryHitIndices_mono G _ hhalf S)).trans hdet
  refine ⟨?_, ?_, ?_, hpair⟩
  · intro x
    apply tripleNearIndices_card G o ell R (R / 2) ω k hfit hbudget S
    intro y
    apply (Finset.card_le_card (endpointHitIndices_mono G _ _ _ ?_ S)).trans (hoccupancy y)
    intro v hv
    exact Set.mem_toFinset.mpr (graphBallVertices_mono G y hhalf (Set.mem_toFinset.mp hv))
  · exact (boundaryOtherTripleIndices_card G o ell R (R / 2) ω hfit hbudget S).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hdetHalf) _)
  · exact (sampledOtherTripleIndices_card G _ R S).trans (Nat.add_le_add hdet hrandom)

namespace RegularGraph
variable {N d : ℕ}

/-- A source-F1-shaped event with a fully proved finite failure budget.
The original one-center exception count is required at R+1 to justify the
two-center tree test at R. All other geometric inputs follow from actual
ball excess, degree, and uniform sample counting. -/
theorem localSampling_sourceGeometricGood_failure (g : RegularGraph N d) (o : Fin N)
    (ell R ω k j q t b : ℕ) (hN : 0 < N) (hd : 3 ≤ d)
    (hT : 4 * Nat.card (graphBallVertices g.graph o ell) ≤ N)
    (hmargin : 2 * ell + 2 ≤ R) (hbudget : graphBallExcess g.graph o R ≤ ω)
    (hbad : (nonTreeCenters g.graph (R + 1)).card ≤ b) :
    eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o ell))
      (fun S => ¬ SourceGeometricGood g.graph o ell R ω k j (2 * q * (2 * k + 1)) t S) ≤
      2 * (N : ℝ) * (((Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) *
        (4 * (((d + 1) * (d - 1) ^ R : ℕ) : ℝ) / N)) ^ (k + 1)) +
      (4 * (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) ^ 2 *
        (((d + 1) * (d - 1) ^ R : ℕ) : ℝ) / N) ^ (j + 1) +
      ((((Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) ^ 2) *
        (8 * (((d + 1) * (d - 1) ^ R : ℕ) : ℝ) / N)) ^ q) +
      ((Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) *
        (4 * (b : ℝ) / N)) ^ (t + 1) := by
  let T := graphBallVertices g.graph o ell
  let w := localSamplingWeight g.graph T
  let P₁ : LocalSamplingFiber g.graph T → Prop := fun S => ∃ x : Fin N,
    k + 1 ≤ (endpointHitIndices g.graph T (graphBallVertices g.graph x R).toFinset S).card
  let P₂ : LocalSamplingFiber g.graph T → Prop := fun S =>
    j + 1 ≤ (sampledBoundaryHitIndices g.graph T R S).card
  let P₃ : LocalSamplingFiber g.graph T → Prop := fun S =>
    2 * q * (2 * k + 1) ≤ (sampledEdgeCollisionGraph g.graph T R S).support.toFinset.card
  let P₄ : LocalSamplingFiber g.graph T → Prop := fun S =>
    t + 1 ≤ (nonTreeSampledPairIndices g.graph T R S).card
  have hcover : ∀ S, ¬ SourceGeometricGood g.graph o ell R ω k j (2 * q * (2 * k + 1)) t S →
      P₁ S ∨ P₂ S ∨ P₃ S ∨ P₄ S := by
    intro S hS
    by_cases h₁ : P₁ S
    · exact Or.inl h₁
    by_cases h₂ : P₂ S
    · exact Or.inr (Or.inl h₂)
    by_cases h₃ : P₃ S
    · exact Or.inr (Or.inr (Or.inl h₃))
    by_cases h₄ : P₄ S
    · exact Or.inr (Or.inr (Or.inr h₄))
    dsimp only [P₁, P₂, P₃, P₄, T] at h₁ h₂ h₃ h₄
    exfalso
    apply hS
    apply sourceGeometricGood_of_counts g.graph o ell R ω k j _ t hmargin hbudget S
    · intro x
      have hx := not_exists.mp h₁ x
      omega
    · omega
    · omega
    · omega
  have hmass := eventMass_mono w finiteUniformWeight_nonneg hcover
  have hunion : eventMass w (fun S => P₁ S ∨ P₂ S ∨ P₃ S ∨ P₄ S) ≤
      eventMass w P₁ + (eventMass w P₂ + (eventMass w P₃ + eventMass w P₄)) := by
    apply (eventMass_union_le w finiteUniformWeight_nonneg P₁ _).trans
    apply add_le_add_left
    apply (eventMass_union_le w finiteUniformWeight_nonneg P₂ _).trans
    exact add_le_add_left (eventMass_union_le w finiteUniformWeight_nonneg P₃ P₄) _
  have h₁ := g.localSampling_any_near_vertex_tail T hN hd hT R (k + 1)
  have h₂ := g.localSampling_boundary_neighborhood_tail T hN hd hT R (j + 1)
  have h₃ := g.localSampling_many_sampled_edge_collisions T hN hd hT R k q
  have h₄ := g.localSampling_nonTree_pair_tail T hN (by omega) hT R b (t + 1) hbad
  apply (hmass.trans hunion).trans
  have hsum := add_le_add h₁ (add_le_add h₂ (add_le_add h₃ h₄))
  convert hsum using 1
  ring

end RegularGraph
end LocalLaw
