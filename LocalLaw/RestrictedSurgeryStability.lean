import LocalLaw.RestrictedPerturbationIdentity
import LocalLaw.SourceEndpointPerturbation
import LocalLaw.SourceEndpointApproximation
import LocalLaw.EndpointKernelRows
import LocalLaw.FiniteRankSurgery

/-!
# Genuine physical and finite-model endpoint surgery stability

The old source pair approximation is localized to one actual restriction.
Saturation and graph support prove identical physical/model updates. The
new finite reference class and component endpoint count prove the needed
Green sums. The resulting new endpoint error is a conclusion.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance restrictedSurgeryStabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def endpointSurgeryCouplingCap (d : ℕ) : ℝ := 2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)

def endpointSurgeryModelRowCap (d m : ℕ) : ℝ := 2 * (m : ℝ) * finiteExtraReferenceConstant d

namespace DeficientGraph
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] {d : ℕ}

/-- All physical and finite inverse identities and all Green sum estimates
are derived; only actual source data and finite geometric conditions remain. -/
theorem restricted_endpoint_surgery_stability (g h : DeficientGraph V d)
    (hd : 3 ≤ d) (S : Set V) (e : I ↪ S) (r Rold Rnew m : ℕ) (z q : ℂ)
    (hz : 0 < z.im) (hq : 0 ≤ q.im) (B C1 ε L A : ℝ) (hB : ‖z‖ ≤ B)
    (num : SourceObservationBounds d r z B C1 ε L A)
    (hsatG : ∀ v, g.graph.degree v + g.deficit v = d)
    (hsatH : ∀ v, h.graph.degree v + h.deficit v = d)
    (hgraph : ∀ x y, x ∉ Set.range (fun i => (e i).val) ∨ y ∉ Set.range (fun i => (e i).val) →
      (g.graph.Adj x y ↔ h.graph.Adj x y))
    (hbudgetOld : (g.restrict S).ComponentFiniteReferenceBudget)
    (hbudgetNew : (h.restrict S).ComponentFiniteReferenceBudget)
    (hdiamOld : ∀ x y, (g.restrict S).graph.dist x y ≤ Rold)
    (hdiamNew : ∀ x y, (h.restrict S).graph.dist x y ≤ Rnew)
    (hRoldlog : (Rold : ℝ) + 1 ≤ A * L) (hRnewlog : (Rnew : ℝ) + 1 ≤ A * L)
    (hcapture : ∀ i, graphBallVertices g.graph (e i).val r ⊆ S)
    (hcount : ∀ c : (h.restrict S).graph.ConnectedComponent, Nat.card {i : I // e i ∈ c.supp} ≤ m)
    (hprior : ‖q - semicircleRoot z‖ ≤ C1 * scalarScale (spectralScale z) ε)
    (hpair : ∀ i j, ‖g.G z (e i).val (e j).val - g.P r z q (e i).val (e j).val‖ ≤ C1 * L ^ 3 * ε)
    (hsmall : (Fintype.card I : ℝ) * (1 + endpointSurgeryModelRowCap d m * endpointSurgeryCouplingCap d) *
      endpointSurgeryCouplingCap d * (2 * C1 * L ^ 3 * ε) ≤ 1 / 2) :
    ∀ i j, ‖h.G z (e i).val (e j).val - (h.restrict S).extensionGreen q z (e i) (e j)‖ ≤
      4 * (1 + endpointSurgeryModelRowCap d m * endpointSurgeryCouplingCap d) ^ 2 * C1 * L ^ 3 * ε := by
  let f : I ↪ V := ⟨fun i => (e i).val, fun _ _ he => e.injective (Subtype.ext he)⟩
  let R := (g.G z).submatrix f f
  let T := (h.G z).submatrix f f
  let P := ((g.restrict S).extensionGreen q z).submatrix e e
  let Q := ((h.restrict S).extensionGreen q z).submatrix e e
  let W := (h.H - g.H).submatrix f f
  let C := endpointSurgeryModelRowCap d m
  let w := endpointSurgeryCouplingCap d
  let δ := 2 * C1 * L ^ 3 * ε
  have hC : 0 ≤ C := by dsimp only [C, endpointSurgeryModelRowCap]; have hh := finiteExtraReferenceConstant_ge_one d hd; positivity
  have hw : 0 ≤ w := by dsimp only [w, endpointSurgeryCouplingCap]; positivity
  have hε : 0 ≤ ε := num.error_nonnegative
  have hC1 : 0 ≤ C1 := (by norm_num : (0 : ℝ) ≤ 1).trans num.coefficient_one
  have hL : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 1).trans num.log_one
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hphysical : ∀ x y, x ∉ Set.range f ∨ y ∉ Set.range f → (h.H - g.H) x y = 0 := by
    intro x y hxy
    have hagree := hgraph x y hxy
    simp only [H, normalizedAdjacency, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, SimpleGraph.adjMatrix_apply]
    rw [← hagree, sub_self]
  have hphysicalUpdate := green_embedded_finite_rank_updates g.H h.H
    (normalizedAdjacency_isHermitian g.graph d) (normalizedAdjacency_isHermitian h.graph d)
    f hphysical z hz
  have hT : T + R * W * T = R := hphysicalUpdate.1
  have hmodelUpdate := g.restrict_endpoint_inverse_updates h hd S e hsatG hsatH hgraph q z hz hq
  have hQ : Q + Q * W * P = P := hmodelUpdate.2
  have hE : ∀ i j, ‖(R - P) i j‖ ≤ δ :=
    g.source_endpoint_restriction_approximation hd S e r Rold z q hz hq B C1 ε L A hB num
      hbudgetOld hdiamOld hRoldlog hcapture hprior hpair
  have hscaled : 0 ≤ C1 ^ 2 * ε := mul_nonneg (sq_nonneg C1) hε
  have hprior' := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) hε num.coefficient_one)
  have hfeedback := (weak_localization_feedback_budgets d hd z q hz B (C1 ^ 2 * ε) L A
    hscaled num.log_one num.log_cap_nonnegative num.error_scaled hprior' Rnew (4 * r + 1)
      hRnewlog num.pair_log num.localization_large).1
  have hrows := (h.restrict S).componentwise_endpoint_green_rows hd hbudgetNew e m hcount
    q z hz hq Rnew hdiamNew hfeedback
  have hQrow : ∀ i, ∑ j, ‖Q i j‖ ≤ C := fun i => hrows.1 (e i)
  have hQcol : ∀ j, ∑ i, ‖Q i j‖ ≤ C := fun j => hrows.2 (e j)
  have hWrow : ∀ i, ∑ j, ‖W i j‖ ≤ w :=
    normalizedAdjacency_difference_endpoint_row_bound g.graph h.graph d g.degree_le h.degree_le f
  have hWcol : ∀ j, ∑ i, ‖W i j‖ ≤ w :=
    normalizedAdjacency_difference_endpoint_column_bound g.graph h.graph d g.degree_le h.degree_le f
  intro i j
  have hh := surgery_entry_stability R T P Q W hT hQ C w δ hC hw hδ hQrow hQcol hWrow hWcol hE hsmall i j
  exact hh.trans_eq (by dsimp only [δ]; ring)

end DeficientGraph
end LocalLaw
