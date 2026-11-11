import LocalLaw.SourceGreenCaps
import LocalLaw.DeletedDiagonalReference

/-! # Physical entry and pivot caps from genuine local reference models

The finite reference class gives entry bounds. A diagonal lower bound is
used only for the zero-extra-deficit base class; the extended class provides
entry caps alone. Approximation and perturbation errors are explicit finite
numerical inputs, with no physical Green cap among the hypotheses.
-/

noncomputable section
namespace LocalLaw

local instance localReferenceCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def commonGreenEntryCap (d : ℕ) : ℝ := finiteExtraReferenceConstant d + 2

theorem sourceGreenEntryCap_le_common (d : ℕ) (hd : 3 ≤ d) :
    sourceGreenEntryCap d ≤ commonGreenEntryCap d := by
  exact add_le_add_right (finiteReferenceConstant_le_extra d hd) 2

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem base_reference_approximation_entry_cap (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected) (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ finiteOmega d)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (D : ℕ) (hD : ∀ i j, g.graph.dist i j ≤ D)
    (small : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * ((D : ℝ) + 1) ≤ 1 / 2)
    (i j : V) (x : ℂ) (E : ℝ) (happrox : ‖x - g.extensionGreen q z i j‖ ≤ E)
    (hE : E ≤ 1) (hchange : pairSensitivityConstant d * ‖q - semicircleRoot z‖ ≤ 1) :
    ‖x‖ ≤ sourceGreenEntryCap d := by
  have hC : 0 ≤ finiteReferenceConstant d :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (finiteReferenceConstant_ge_one d hd)
  have href := (finiteOmega_reference_bounds d hd g hG hbudget z hz).1 i j
  have ht : ‖-semicircleRoot z * treeEdgeWeight d‖ ≤ 1 := by
    have hh := physicalTransfer_sq_le_half d hd z
    unfold physicalTransfer at hh
    nlinarith [norm_nonneg (-semicircleRoot z * treeEdgeWeight d)]
  have hrefCap : ‖g.extensionGreen (semicircleRoot z) z i j‖ ≤ finiteReferenceConstant d :=
    href.trans (mul_le_of_le_one_right hC (pow_le_one₀ (norm_nonneg _) ht))
  have hpert := g.finiteOmega_boundary_uniform_stability hd hG hbudget z q hz hq D hD small i j
  change ‖g.extensionGreen q z i j - g.extensionGreen (semicircleRoot z) z i j‖ ≤
    pairSensitivityConstant d * ‖q - semicircleRoot z‖ at hpert
  have hnorm := (norm_sub_le_norm_sub_add_norm_sub x (g.extensionGreen q z i j)
    (g.extensionGreen (semicircleRoot z) z i j)).trans (add_le_add happrox hpert)
  have htriangle := norm_add_le (g.extensionGreen (semicircleRoot z) z i j)
    (x - g.extensionGreen (semicircleRoot z) z i j)
  rw [add_sub_cancel] at htriangle
  change ‖x‖ ≤ finiteReferenceConstant d + 2
  linarith

theorem base_reference_approximation_pivot_cap (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected) (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ finiteOmega d)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (B : ℝ) (hB : ‖z‖ ≤ B)
    (D : ℕ) (hD : ∀ i j, g.graph.dist i j ≤ D)
    (small : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * ((D : ℝ) + 1) ≤ 1 / 2)
    (i : V) (x : ℂ) (E : ℝ) (happrox : ‖x - g.extensionGreen q z i i‖ ≤ E)
    (herror : E + pairSensitivityConstant d * ‖q - semicircleRoot z‖ ≤
      1 / (2 * finiteReferenceConstant d * (B + 2))) :
    ‖x⁻¹‖ ≤ sourceGreenPivotCap d B := by
  have hC := finiteReferenceConstant_ge_one d hd
  have hB0 : 0 ≤ B := (norm_nonneg z).trans hB
  have href := (finiteOmega_reference_diagonal_bounds d hd g hG hbudget z hz B hB i).1
  have hpert := g.finiteOmega_boundary_uniform_stability hd hG hbudget z q hz hq D hD small i i
  change ‖g.extensionGreen q z i i - g.extensionGreen (semicircleRoot z) z i i‖ ≤
    pairSensitivityConstant d * ‖q - semicircleRoot z‖ at hpert
  have hdist := (norm_sub_le_norm_sub_add_norm_sub x (g.extensionGreen q z i i)
    (g.extensionGreen (semicircleRoot z) z i i)).trans (add_le_add happrox hpert)
  have hpositive : 0 < 1 / (2 * finiteReferenceConstant d * (B + 2)) := by positivity
  have hsplit : 1 / (finiteReferenceConstant d * (B + 2)) =
      2 * (1 / (2 * finiteReferenceConstant d * (B + 2))) := by field_simp; ring
  have hlower : 1 / (2 * finiteReferenceConstant d * (B + 2)) ≤ ‖x‖ := by
    have hh := norm_sub_norm_le (g.extensionGreen (semicircleRoot z) z i i) x
    rw [norm_sub_rev] at hh
    linarith
  rw [norm_inv]
  calc
    _ ≤ (1 / (2 * finiteReferenceConstant d * (B + 2)))⁻¹ := inv_anti₀ hpositive hlower
    _ = sourceGreenPivotCap d B := by simp [sourceGreenPivotCap]

theorem finite_reference_approximation_entry_cap (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected) (hbudget : g.FiniteReferenceBudget)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (D : ℕ) (hD : ∀ i j, g.graph.dist i j ≤ D)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((D : ℝ) + 1) ≤ 1 / 2)
    (i j : V) (x : ℂ) (E : ℝ) (happrox : ‖x - g.extensionGreen q z i j‖ ≤ E)
    (hE : E ≤ 1) (hchange : deletedSensitivityConstant d * ‖q - semicircleRoot z‖ ≤ 1) :
    ‖x‖ ≤ commonGreenEntryCap d := by
  have hC : 0 ≤ finiteExtraReferenceConstant d :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have href := (g.finite_class_reference_bounds hd hG hbudget z hz).1 i j
  have ht : physicalTransfer d z ≤ 1 := by nlinarith [physicalTransfer_sq_le_half d hd z, (physicalTransfer_pos d hd z).le]
  have hrefCap : ‖g.extensionGreen (semicircleRoot z) z i j‖ ≤ finiteExtraReferenceConstant d :=
    href.trans (mul_le_of_le_one_right hC (pow_le_one₀ (physicalTransfer_pos d hd z).le ht))
  have hexcess : graphExcess g.graph ≤ finiteOmega d + 1 := by
    have hh := hbudget.complexity_le
    omega
  have hpert := g.reference_boundary_uniform_stability hd hG (finiteOmega d + 1) hexcess z q hz hq
    (finiteExtraReferenceConstant d) hC D hD (g.finite_class_reference_bounds hd hG hbudget z hz).1 small i j
  change ‖g.extensionGreen q z i j - g.extensionGreen (semicircleRoot z) z i j‖ ≤
    deletedSensitivityConstant d * ‖q - semicircleRoot z‖ at hpert
  have hnorm := (norm_sub_le_norm_sub_add_norm_sub x (g.extensionGreen q z i j)
    (g.extensionGreen (semicircleRoot z) z i j)).trans (add_le_add happrox hpert)
  have htriangle := norm_add_le (g.extensionGreen (semicircleRoot z) z i j)
    (x - g.extensionGreen (semicircleRoot z) z i j)
  rw [add_sub_cancel] at htriangle
  change ‖x‖ ≤ finiteExtraReferenceConstant d + 2
  linarith

end DeficientGraph
end LocalLaw
