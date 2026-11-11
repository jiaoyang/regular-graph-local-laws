import LocalLaw.ResamplingGeometricEvent

/-!
# The geometric event including own-sample boundary separation

The source (5.31) pair tests exclude beta=alpha and therefore do not control
a sample close to its own boundary root. Such samples can fail the I-test.
The stronger event here explicitly bounds all sampled edges near boundary
roots, including their own root. Its added failure term is already controlled
by the proved independent boundary-neighborhood estimate.
-/

noncomputable section
namespace LocalLaw

local instance sourceFullGeometricEventDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V]

def SourceFullGeometricGood (G : SimpleGraph V) (o : V) (ell R ω k j C t : ℕ)
    (S : LocalSamplingFiber G (graphBallVertices G o ell)) : Prop :=
  SourceGeometricGood G o ell R ω k j C t S ∧
    (sampledBoundaryHitIndices G (graphBallVertices G o ell) R S).card ≤ j

namespace RegularGraph
variable {N d : ℕ}

theorem localSampling_sourceFullGeometricGood_failure_add (g : RegularGraph N d) (o : Fin N)
    (ell R ω k j C t : ℕ) (hN : 0 < N) (hd : 3 ≤ d)
    (hT : 4 * Nat.card (graphBallVertices g.graph o ell) ≤ N) :
    eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o ell))
      (fun S => ¬ SourceFullGeometricGood g.graph o ell R ω k j C t S) ≤
      eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o ell))
        (fun S => ¬ SourceGeometricGood g.graph o ell R ω k j C t S) +
      (4 * (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) ^ 2 *
        (((d + 1) * (d - 1) ^ R : ℕ) : ℝ) / N) ^ (j + 1) := by
  have hcover : ∀ S, ¬ SourceFullGeometricGood g.graph o ell R ω k j C t S →
      (¬ SourceGeometricGood g.graph o ell R ω k j C t S) ∨
        j + 1 ≤ (sampledBoundaryHitIndices g.graph (graphBallVertices g.graph o ell) R S).card := by
    intro S hS
    by_cases hgood : SourceGeometricGood g.graph o ell R ω k j C t S
    · apply Or.inr
      by_contra hcount
      exact hS ⟨hgood, by omega⟩
    · exact Or.inl hgood
  apply (eventMass_mono _ finiteUniformWeight_nonneg hcover).trans
  apply (eventMass_union_le _ finiteUniformWeight_nonneg _ _).trans
  exact add_le_add_left (g.localSampling_boundary_neighborhood_tail _ hN hd hT R (j + 1)) _

/-- The fully proved finite five-term good-data estimate; the two identical
boundary-hit terms have been collected into their explicit factor two. -/
theorem localSampling_sourceFullGeometricGood_failure (g : RegularGraph N d) (o : Fin N)
    (ell R ω k j q t b : ℕ) (hN : 0 < N) (hd : 3 ≤ d)
    (hT : 4 * Nat.card (graphBallVertices g.graph o ell) ≤ N)
    (hmargin : 2 * ell + 2 ≤ R) (hbudget : graphBallExcess g.graph o R ≤ ω)
    (hbad : (nonTreeCenters g.graph (R + 1)).card ≤ b) :
    eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o ell))
      (fun S => ¬ SourceFullGeometricGood g.graph o ell R ω k j (2 * q * (2 * k + 1)) t S) ≤
      2 * (N : ℝ) * (((Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) *
        (4 * (((d + 1) * (d - 1) ^ R : ℕ) : ℝ) / N)) ^ (k + 1)) +
      2 * (4 * (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) ^ 2 *
        (((d + 1) * (d - 1) ^ R : ℕ) : ℝ) / N) ^ (j + 1) +
      ((((Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) ^ 2) *
        (8 * (((d + 1) * (d - 1) ^ R : ℕ) : ℝ) / N)) ^ q) +
      ((Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) *
        (4 * (b : ℝ) / N)) ^ (t + 1) := by
  apply (g.localSampling_sourceFullGeometricGood_failure_add o ell R ω k j _ t hN hd hT).trans
  have h := add_le_add_right (g.localSampling_sourceGeometricGood_failure
    o ell R ω k j q t b hN hd hT hmargin hbudget hbad)
    ((4 * (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) ^ 2 *
      (((d + 1) * (d - 1) ^ R : ℕ) : ℝ) / N) ^ (j + 1))
  convert h using 1
  ring

end RegularGraph
end LocalLaw
