import LocalLaw.SingletonBallModel
import LocalLaw.IndependentRadiusEvents
import LocalLaw.GraphExcessSurgery
import LocalLaw.SourceObservationParameters

/-! # Base class and diameter of the deterministic old central model

This model is an ordinary expanded old root ball and contains no sampled
vertices in its definition. Its source deficit is zero. The structural-plus
small-ball clause gives the actual base class and a logarithmic diameter.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance deterministicCentralBudgetDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

def deterministicCentralModel (g : RegularGraph N d) (o : Fin N) (ell r : ℕ) :
    DeficientGraph (graphBallVertices g.graph o (ell + r + 1)) d :=
  g.deficient.restrict (graphBallVertices g.graph o (ell + r + 1))

theorem deterministicCentralModel_connected (g : RegularGraph N d) (o : Fin N) (ell r : ℕ) :
    (g.deterministicCentralModel o ell r).graph.Connected := graphBall_connected _ _ _

theorem deterministicCentralModel_deficit_zero (g : RegularGraph N d) (o : Fin N) (ell r : ℕ)
    (v : graphBallVertices g.graph o (ell + r + 1)) :
    (g.deterministicCentralModel o ell r).deficit v = 0 := rfl

theorem deterministicCentralModel_distance_bound (g : RegularGraph N d) (o : Fin N) (ell r : ℕ)
    (x y : graphBallVertices g.graph o (ell + r + 1)) :
    (g.deterministicCentralModel o ell r).graph.dist x y ≤ 2 * (ell + r + 1) :=
  graphBall_distance_le_twice_radius g.graph o (ell + r + 1) x y

theorem deterministicCentralModel_base_budget (g : RegularGraph N d) (o : Fin N)
    (ell r R : ℕ) (hmargin : ell + r + 1 ≤ R)
    (hbudget : graphBallExcess g.graph o R ≤ finiteOmega d) :
    (∑ v, (g.deterministicCentralModel o ell r).deficit v) +
      graphExcess (g.deterministicCentralModel o ell r).graph ≤ finiteOmega d := by
  simp only [g.deterministicCentralModel_deficit_zero, Finset.sum_const_zero, zero_add]
  exact (graphBallExcess_mono_radius g.graph o hmargin).trans hbudget

theorem deterministicCentralModel_component_budget (g : RegularGraph N d) (o : Fin N)
    (ell r R : ℕ) (hmargin : ell + r + 1 ≤ R)
    (hbudget : graphBallExcess g.graph o R ≤ finiteOmega d) :
    (g.deterministicCentralModel o ell r).ComponentReferenceBudget := by
  apply (g.deterministicCentralModel o ell r).connected_zero_component_budget
    (g.deterministicCentralModel_connected o ell r) (g.deterministicCentralModel_deficit_zero o ell r)
  exact (graphBallExcess_mono_radius g.graph o hmargin).trans hbudget

theorem sourceOmegaPlus_deterministicCentralModel_budget (g : RegularGraph N d)
    (a r rError R ell Cq badCount : ℕ) (C1 : ℝ) (o : Fin N) (z : ℂ)
    (h : g.SourceOmegaPlusWithRadii a r rError R ell (finiteOmega d) Cq badCount C1 o z)
    (hmargin : ell + r + 1 ≤ R / 8) :
    (g.deterministicCentralModel o ell r).ComponentReferenceBudget ∧
      (g.deterministicCentralModel o ell r).FiniteReferenceBudget :=
  ⟨g.deterministicCentralModel_component_budget o ell r (R / 8) hmargin (h.structural.1 o),
    Or.inl (g.deterministicCentralModel_base_budget o ell r (R / 8) hmargin (h.structural.1 o))⟩

theorem deterministicCentralModel_diameter_le_observation (d ell r : ℕ) (hell : ell ≤ r) :
    2 * (ell + r + 1) ≤ singletonObservationDiameter d r := by
  unfold singletonObservationDiameter
  nlinarith only [Nat.zero_le (finiteOmega d), hell]

theorem deterministicCentralModel_log_diameter (g : RegularGraph N d) (o : Fin N)
    (ell r : ℕ) (hell : ell ≤ r) (z : ℂ) (B C ε L A : ℝ)
    (S : SourceObservationBounds d r z B C ε L A)
    (x y : graphBallVertices g.graph o (ell + r + 1)) :
    ((g.deterministicCentralModel o ell r).graph.dist x y : ℝ) + 1 ≤ A * L := by
  have hnat := (g.deterministicCentralModel_distance_bound o ell r x y).trans
    (deterministicCentralModel_diameter_le_observation d ell r hell)
  exact (add_le_add_right (Nat.cast_le.mpr hnat) 1).trans S.diameter_log

end RegularGraph
end LocalLaw
