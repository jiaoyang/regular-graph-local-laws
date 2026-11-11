import LocalLaw.SmallRadiusRejectedLabels
import LocalLaw.GeometricSamplingParameters

/-! # Raw sampling counts sufficient for source-plus rejection control

The sampled radius is independent of the old structural radius. All four
probability estimates are genuine finite uniform-sampling conclusions.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance surgerySamplingCountsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V]

def SurgerySamplingGood (G : SimpleGraph V) (T : Set V) (M k j q t : ℕ)
    (S : LocalSamplingFiber G T) : Prop :=
  (sampledBoundaryHitIndices G T M S).card ≤ j ∧
    (sampledEdgeCollisionGraph G T M S).support.toFinset.card ≤ 2 * q * (2 * k + 1) ∧
    (nonTreeSampledPairIndices G T M S).card ≤ t

theorem rejected_resampling_count_of_surgerySamplingGood (G : SimpleGraph V) (o : V)
    (ell R M Cq k j q t : ℕ) (hmargin : ell + 1 + R / 4 ≤ R / 2)
    (hsel : R / 4 ≤ M) (hsep : 2 * (R / 4) + 1 ≤ M)
    (hbudget : graphBallExcess G o (R / 2) ≤ Cq)
    (S : LocalSamplingFiber G (graphBallVertices G o ell))
    (hgood : SurgerySamplingGood G (graphBallVertices G o ell) M k j q t S) :
    (rejectedResamplingIndices G (graphBallVertices G o ell) (R / 4) S).card ≤
      3 * Cq + 2 * j * (Cq + 2) + 2 * q * (2 * k + 1) + t := by
  have hbase := rejectedResamplingIndices_card_five_sets G o ell (R / 4) (R / 4) M
    le_rfl hsel hsep S
  have ha := boundary_nonTree_ball_count G o ell (R / 2) (R / 4) Cq hmargin hbudget
  have hb := boundaryOtherTripleIndices_card G o ell (R / 2) (R / 4) Cq hmargin hbudget S
  have hh := (Finset.card_le_card (sampledBoundaryHitIndices_mono G _ hsel S)).trans hgood.1
  have ho := (sampledOtherTripleIndices_card G _ M S).trans (Nat.add_le_add hgood.1 hgood.2.1)
  have hp := hgood.2.2
  have hm := hgood.1
  have hmul := Nat.mul_le_mul_right (2 * (Cq + 1)) hh
  nlinarith

namespace RegularGraph
variable {N d : ℕ}

theorem localSampling_surgerySamplingGood_failure (g : RegularGraph N d) (T : Set (Fin N))
    (M k j q t b : ℕ) (hN : 0 < N) (hd : 3 ≤ d)
    (hT : 4 * Nat.card T ≤ N) (hbad : (nonTreeCenters g.graph (M + 1)).card ≤ b) :
    eventMass (localSamplingWeight g.graph T) (fun S => ¬SurgerySamplingGood g.graph T M k j q t S) ≤
      2 * (N : ℝ) * (((Nat.card (BoundaryOrientedEdge g.graph T) : ℝ) *
        (4 * (((d + 1) * (d - 1) ^ M : ℕ) : ℝ) / N)) ^ (k + 1)) +
      (4 * (Nat.card (BoundaryOrientedEdge g.graph T) : ℝ) ^ 2 *
        (((d + 1) * (d - 1) ^ M : ℕ) : ℝ) / N) ^ (j + 1) +
      (((Nat.card (BoundaryOrientedEdge g.graph T) : ℝ) ^ 2) *
        (8 * (((d + 1) * (d - 1) ^ M : ℕ) : ℝ) / N)) ^ q +
      ((Nat.card (BoundaryOrientedEdge g.graph T) : ℝ) * (4 * (b : ℝ) / N)) ^ (t + 1) := by
  let w := localSamplingWeight g.graph T
  let P₁ : LocalSamplingFiber g.graph T → Prop := fun S => ∃ x : Fin N,
    k + 1 ≤ (endpointHitIndices g.graph T (graphBallVertices g.graph x M).toFinset S).card
  let P₂ : LocalSamplingFiber g.graph T → Prop := fun S =>
    j + 1 ≤ (sampledBoundaryHitIndices g.graph T M S).card
  let P₃ : LocalSamplingFiber g.graph T → Prop := fun S =>
    2 * q * (2 * k + 1) ≤ (sampledEdgeCollisionGraph g.graph T M S).support.toFinset.card
  let P₄ : LocalSamplingFiber g.graph T → Prop := fun S =>
    t + 1 ≤ (nonTreeSampledPairIndices g.graph T M S).card
  have hcover : ∀ S, ¬SurgerySamplingGood g.graph T M k j q t S → P₁ S ∨ P₂ S ∨ P₃ S ∨ P₄ S := by
    intro S hS
    by_cases h₂ : P₂ S
    · exact Or.inr (Or.inl h₂)
    by_cases h₃ : P₃ S
    · exact Or.inr (Or.inr (Or.inl h₃))
    by_cases h₄ : P₄ S
    · exact Or.inr (Or.inr (Or.inr h₄))
    exact False.elim (hS ⟨by dsimp only [P₂] at h₂; omega,
      by dsimp only [P₃] at h₃; omega, by dsimp only [P₄] at h₄; omega⟩)
  have hmass := eventMass_mono w finiteUniformWeight_nonneg hcover
  have hunion : eventMass w (fun S => P₁ S ∨ P₂ S ∨ P₃ S ∨ P₄ S) ≤
      eventMass w P₁ + (eventMass w P₂ + (eventMass w P₃ + eventMass w P₄)) := by
    apply (eventMass_union_le w finiteUniformWeight_nonneg P₁ _).trans
    apply add_le_add_left
    apply (eventMass_union_le w finiteUniformWeight_nonneg P₂ _).trans
    exact add_le_add_left (eventMass_union_le w finiteUniformWeight_nonneg P₃ P₄) _
  have h₁ := g.localSampling_any_near_vertex_tail T hN hd hT M (k + 1)
  have h₂ := g.localSampling_boundary_neighborhood_tail T hN hd hT M (j + 1)
  have h₃ := g.localSampling_many_sampled_edge_collisions T hN hd hT M k q
  have h₄ := g.localSampling_nonTree_pair_tail T hN (by omega) hT M b (t + 1) hbad
  apply (hmass.trans hunion).trans
  have hsum := add_le_add h₁ (add_le_add h₂ (add_le_add h₃ h₄))
  convert hsum using 1
  ring

end RegularGraph
end LocalLaw
