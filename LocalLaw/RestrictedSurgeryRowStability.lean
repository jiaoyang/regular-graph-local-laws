import LocalLaw.RestrictedSurgeryStability
import LocalLaw.SourceEndpointPerturbation
import LocalLaw.SourceEndpointApproximation
import LocalLaw.EndpointKernelRows
import LocalLaw.FiniteRankSurgery

/-!
# Physical surgery from independently established switched model rows

The old source pair approximation is localized to one actual restriction.
Saturation and graph support prove identical physical/model updates. Any
proved new row and column bounds suffice, without a new finite class.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance restrictedSurgeryRowStabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace DeficientGraph
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] {d : ℕ}

/-- Actual inverse updates propagate old source errors using proved new
model row and column bounds. No new model approximation is assumed. -/
theorem restricted_endpoint_surgery_stability_of_rows (g h : DeficientGraph V d)
    (hd : 3 ≤ d) (S : Set V) (e : I ↪ S) (r Rold : ℕ) (z q : ℂ)
    (hz : 0 < z.im) (hq : 0 ≤ q.im) (B C1 ε L A : ℝ) (hB : ‖z‖ ≤ B)
    (num : SourceObservationBounds d r z B C1 ε L A)
    (hsatG : ∀ v, g.graph.degree v + g.deficit v = d)
    (hsatH : ∀ v, h.graph.degree v + h.deficit v = d)
    (hgraph : ∀ x y, x ∉ Set.range (fun i => (e i).val) ∨ y ∉ Set.range (fun i => (e i).val) →
      (g.graph.Adj x y ↔ h.graph.Adj x y))
    (hbudgetOld : (g.restrict S).ComponentFiniteReferenceBudget)
    (hdiamOld : ∀ x y, (g.restrict S).graph.dist x y ≤ Rold)
    (hRoldlog : (Rold : ℝ) + 1 ≤ A * L)
    (hcapture : ∀ i, graphBallVertices g.graph (e i).val r ⊆ S)
    (C : ℝ) (hC : 0 ≤ C)
    (hQrow : ∀ i, ∑ j, ‖(h.restrict S).extensionGreen q z (e i) (e j)‖ ≤ C)
    (hQcol : ∀ j, ∑ i, ‖(h.restrict S).extensionGreen q z (e i) (e j)‖ ≤ C)
    (hprior : ‖q - semicircleRoot z‖ ≤ C1 * scalarScale (spectralScale z) ε)
    (hpair : ∀ i j, ‖g.G z (e i).val (e j).val - g.P r z q (e i).val (e j).val‖ ≤ C1 * L ^ 3 * ε)
    (hsmall : (Fintype.card I : ℝ) * (1 + C * endpointSurgeryCouplingCap d) *
      endpointSurgeryCouplingCap d * (2 * C1 * L ^ 3 * ε) ≤ 1 / 2) :
    ∀ i j, ‖h.G z (e i).val (e j).val - (h.restrict S).extensionGreen q z (e i) (e j)‖ ≤
      4 * (1 + C * endpointSurgeryCouplingCap d) ^ 2 * C1 * L ^ 3 * ε := by
  let f : I ↪ V := ⟨fun i => (e i).val, fun _ _ he => e.injective (Subtype.ext he)⟩
  let R := (g.G z).submatrix f f
  let T := (h.G z).submatrix f f
  let P := ((g.restrict S).extensionGreen q z).submatrix e e
  let Q := ((h.restrict S).extensionGreen q z).submatrix e e
  let W := (h.H - g.H).submatrix f f
  let w := endpointSurgeryCouplingCap d
  let δ := 2 * C1 * L ^ 3 * ε
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
  have hWrow : ∀ i, ∑ j, ‖W i j‖ ≤ w :=
    normalizedAdjacency_difference_endpoint_row_bound g.graph h.graph d g.degree_le h.degree_le f
  have hWcol : ∀ j, ∑ i, ‖W i j‖ ≤ w :=
    normalizedAdjacency_difference_endpoint_column_bound g.graph h.graph d g.degree_le h.degree_le f
  intro i j
  have hh := surgery_entry_stability R T P Q W hT hQ C w δ hC hw hδ hQrow hQcol hWrow hWcol hE hsmall i j
  exact hh.trans_eq (by dsimp only [δ]; ring)

end DeficientGraph
end LocalLaw
