import LocalLaw.ExteriorDeficitComponents
import LocalLaw.GraphExcessSurgery
import LocalLaw.DeficitLocalization

/-!
# Actual connected restrictions remain in the finite reference class

The degree deficit is inherited, and the induced excess cannot increase.
The extra-deficit allowance is retained only when a positive deficit survives.
The clearing operation has exactly the same restricted physical model.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance restrictedReferenceDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

omit [DecidableEq V] in
theorem restrict_deficit_sum_le (g : DeficientGraph V d) (S : Set V) :
    (∑ u, (g.restrict S).deficit u) ≤ ∑ v, g.deficit v := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun v : V => v ∈ S) g.deficit
  change (∑ u : S, g.deficit u.val) ≤ ∑ v, g.deficit v
  simp only [← finsum_eq_sum_of_fintype] at hsplit ⊢
  change finsum (fun u : S => g.deficit u.val) +
    finsum (fun u : {v : V // v ∉ S} => g.deficit u.val) = finsum g.deficit at hsplit
  change finsum (fun u : S => g.deficit u.val) ≤ finsum g.deficit
  exact (Nat.le_add_right _ _).trans_eq hsplit

omit [DecidableEq V] in
theorem restrict_finiteReferenceBudget (g : DeficientGraph V d) (S : Set V)
    (hG : g.graph.Connected) (hS : (g.graph.induce S).Connected)
    (hbudget : g.FiniteReferenceBudget) : (g.restrict S).FiniteReferenceBudget := by
  have hsum := g.restrict_deficit_sum_le S
  have hex : graphExcess (g.restrict S).graph ≤ graphExcess g.graph := by
    have hh := connected_induce_graphExcess_le g.graph S hG hS
    simp only [restrict, graphExcess, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hh ⊢
    exact hh
  have htotal := hbudget.complexity_le
  have hexcess := hbudget.excess_le
  by_cases hpos : ∃ u, 0 < (g.restrict S).deficit u
  · right
    exact ⟨by omega, hpos⟩
  · have hzero : ∀ u, (g.restrict S).deficit u = 0 := by
      intro u
      exact Nat.eq_zero_of_not_pos (fun hu => hpos ⟨u, hu⟩)
    left
    simp only [hzero, Finset.sum_const_zero, zero_add]
    exact hex.trans hexcess

/-- Clearing only exterior deficits leaves the literal restricted model
and its genuine Green matrix exactly unchanged. -/
theorem clearOutsideDeficit_restricted_Green (g : DeficientGraph V d) (S : Set V) (q z : ℂ) :
    ((g.clearOutsideDeficit S).restrict S).extensionGreen q z = (g.restrict S).extensionGreen q z := by
  have hcoeff : ∀ u : S, ((g.clearOutsideDeficit S).restrict S).boundaryCoefficient u =
      (g.restrict S).boundaryCoefficient u := by
    intro u
    simp only [boundaryCoefficient, restrict, clearOutsideDeficit, if_pos u.property]
  have hD : ((g.clearOutsideDeficit S).restrict S).boundaryDiagonal = (g.restrict S).boundaryDiagonal := by
    simp only [boundaryDiagonal, hcoeff]
  change (boundaryMatrix (g.restrict S).H ((g.clearOutsideDeficit S).restrict S).boundaryDiagonal q z)⁻¹ = _
  rw [hD]
  rfl

/-- Actual inherited-deficit local models have the derived perturbed
kernel bound whenever their true intrinsic diameter meets the feedback budget. -/
theorem restricted_finite_class_kernel_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hG : g.graph.Connected) (hS : (g.graph.induce S).Connected)
    (hbudget : g.FiniteReferenceBudget) (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j, (g.graph.induce S).dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2) (i j : S) :
    ‖(g.restrict S).extensionGreen q z i j‖ ≤
      2 * finiteExtraReferenceConstant d * (g.restrict S).referenceDecay z i j :=
  (g.restrict S).finite_class_kernel_bound hd hS (g.restrict_finiteReferenceBudget S hG hS hbudget)
    z q hz hq R hR small i j

end DeficientGraph
end LocalLaw
