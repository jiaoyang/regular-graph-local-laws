import LocalLaw.FullEndpointPerturbation
import LocalLaw.SharpSourceRestriction
import LocalLaw.FiniteRankSurgery

/-! # Full physical endpoint stability with a genuine filled benchmark

Every matrix update and coupling bound is derived from the actual labelled
switching. The only geometric contracts are finite reference classes,
diameters and containment of the old endpoint balls. The new reference row
bound is obtained by summing its proved kernel cap over the actual block.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance fullEndpointStabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def fullEndpointSurgeryError (d : ℕ) (B C1 ε L A : ℝ) : ℝ :=
  (C1 + DeficientGraph.localizationWeakConstant d B A * C1 ^ 2 * L) * ε

def fullEndpointSurgeryRowCap (d n : ℕ) : ℝ := (n : ℝ) * (2 * finiteExtraReferenceConstant d)

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem fullEndpoint_entry_stability_of_geometry (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (boundary : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector r R : ℕ)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (B C1 ε L A : ℝ) (hB : ‖z‖ ≤ B) (num : SourceObservationBounds d r z B C1 ε L A)
    (hOldBudget : (g.filledExteriorModel T ((g.admissibleState T boundary samples).endpointModelVertices selector r)).ComponentFiniteReferenceBudget)
    (hNewBudget : ((g.labelledResampledGraph T boundary samples selector).filledExteriorModel T
      ((g.admissibleState T boundary samples).endpointModelVertices selector r)).ComponentFiniteReferenceBudget)
    (hOldDiam : ∀ x y, (g.filledExteriorModel T
      ((g.admissibleState T boundary samples).endpointModelVertices selector r)).graph.dist x y ≤ R)
    (hNewDiam : ∀ x y, ((g.labelledResampledGraph T boundary samples selector).filledExteriorModel T
      ((g.admissibleState T boundary samples).endpointModelVertices selector r)).graph.dist x y ≤ R)
    (hRlog : (R : ℝ) + 1 ≤ A * L)
    (hcapture : ∀ x : (g.admissibleState T boundary samples).fullEndpointRoots selector,
      graphBallVertices g.graph x.val r ⊆ filledExteriorVertices T
        ((g.admissibleState T boundary samples).endpointModelVertices selector r))
    (hprior : ‖q - semicircleRoot z‖ ≤ C1 * scalarScale (spectralScale z) ε)
    (hweak : ∀ x y, ‖g.G z x y - g.P r z q x y‖ ≤ C1 * ε)
    (hsmall :
      (Nat.card ((g.admissibleState T boundary samples).fullEndpointRoots selector) : ℝ) *
        (1 + fullEndpointSurgeryRowCap d (Nat.card ((g.admissibleState T boundary samples).fullEndpointRoots selector)) *
          (2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1))) *
        (2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) * fullEndpointSurgeryError d B C1 ε L A ≤ 1 / 2) :
    let s := g.admissibleState T boundary samples
    let gnew := g.labelledResampledGraph T boundary samples selector
    let e := s.fullEndpointModelEmbedding selector r
    ∀ i j : s.fullEndpointRoots selector,
      ‖gnew.G z i.val j.val - (gnew.filledExteriorModel T (s.endpointModelVertices selector r)).extensionGreen q z (e i) (e j)‖ ≤
        2 * (1 + fullEndpointSurgeryRowCap d (Nat.card (s.fullEndpointRoots selector)) *
          (2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1))) ^ 2 * fullEndpointSurgeryError d B C1 ε L A := by
  dsimp only
  let s := g.admissibleState T boundary samples
  let gnew := g.labelledResampledGraph T boundary samples selector
  let S := filledExteriorVertices T (s.endpointModelVertices selector r)
  let e := s.fullEndpointModelEmbedding selector r
  let f := s.fullEndpointRootEmbedding selector
  let Rold := (g.G z).submatrix f f
  let Rnew := (gnew.G z).submatrix f f
  let P := ((g.deficient.restrict S).extensionGreen q z).submatrix e e
  let Q := ((gnew.deficient.restrict S).extensionGreen q z).submatrix e e
  let W := (gnew.H - g.H).submatrix f f
  let C := fullEndpointSurgeryRowCap d (Nat.card (s.fullEndpointRoots selector))
  let w := 2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)
  let δ := fullEndpointSurgeryError d B C1 ε L A
  have hCextra : 0 ≤ finiteExtraReferenceConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans
    (finiteExtraReferenceConstant_ge_one d hd)
  have hC : 0 ≤ C := by dsimp only [C, fullEndpointSurgeryRowCap]; positivity
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hprior' := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative num.coefficient_one)
  have hfeedback := DeficientGraph.weak_localization_feedback_budgets d hd z q hz B (C1 ^ 2 * ε) L A
    (mul_nonneg (sq_nonneg C1) num.error_nonnegative) num.log_one num.log_cap_nonnegative
    num.error_scaled hprior' R (4 * r + 1) hRlog num.pair_log num.localization_large
  have ht : physicalTransfer d z ≤ 1 := by
    have hs := physicalTransfer_sq_le_half d hd z
    have hp := (physicalTransfer_pos d hd z).le
    nlinarith
  have hQpoint (i j : s.fullEndpointRoots selector) : ‖Q i j‖ ≤ 2 * finiteExtraReferenceConstant d := by
    have hh := (gnew.deficient.restrict S).componentwise_finite_kernel_decay hd hNewBudget q z hz hq
      R hNewDiam hfeedback.1 (e i) (e j)
    exact hh.trans (by
      have hp := pow_le_one₀ (n := (gnew.deficient.restrict S).graph.dist (e i) (e j))
        (physicalTransfer_pos d hd z).le ht
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * finiteExtraReferenceConstant d))
  have hQrow : ∀ i, ∑ j, ‖Q i j‖ ≤ C := by
    intro i
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hQpoint i j)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, C, fullEndpointSurgeryRowCap,
      Nat.card_eq_fintype_card] using hh
  have hQcol : ∀ j, ∑ i, ‖Q i j‖ ≤ C := by
    intro j
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hQpoint i j)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, C, fullEndpointSurgeryRowCap,
      Nat.card_eq_fintype_card] using hh
  have hE : ∀ i j, ‖(Rold - P) i j‖ ≤ δ := by
    have hpair : ∀ i j, ‖g.deficient.G z (e i).val (e j).val - g.deficient.P r z q (e i).val (e j).val‖ ≤ C1 * ε := by
      intro i j
      rw [g.deficient_P]
      exact hweak _ _
    exact g.deficient.source_weak_restriction_approximation hd S e r R z q hz hq B C1 ε L A hB num
      hOldBudget hOldDiam hRlog hcapture hprior hpair
  have hmass := s.fullResample_endpoint_mass selector d (fun v => (g.regular v).le) f
  have hupdate := g.fullEndpoint_physical_model_updates hd T boundary samples selector r q z hz hq
  intro i j
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hE i i)
  exact surgery_entry_stability Rold Rnew P Q W hupdate.1 hupdate.2.2.2 C w δ hC hw hδ
    hQrow hQcol hmass.1 hmass.2 hE
      (by simpa only [Nat.card_eq_fintype_card, C, w, δ, s] using hsmall) i j

end RegularGraph
end LocalLaw
