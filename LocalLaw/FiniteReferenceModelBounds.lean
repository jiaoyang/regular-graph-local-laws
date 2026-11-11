import LocalLaw.FiniteThresholdStability

/-!
# A common actual finite reference class and perturbed decay bound

Both allowed complexity cases use a single degree-dependent constant. The
kernel estimate is a conclusion of the proved reference class and actual
bounded-excess boundary perturbation, not an additional model assumption.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw

theorem finiteReferenceConstant_le_extra (d : ℕ) (hd : 3 ≤ d) :
    finiteReferenceConstant d ≤ finiteExtraReferenceConstant d := by
  have hC : 0 ≤ finiteReferenceConstant d := le_trans (by norm_num) (finiteReferenceConstant_ge_one d hd)
  dsimp [finiteExtraReferenceConstant, extraDeficitConstant]
  nlinarith [pow_nonneg hC 3, pow_nonneg hC 5]

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

def FiniteReferenceBudget (g : DeficientGraph V d) : Prop :=
  ((∑ v, g.deficit v) + graphExcess g.graph ≤ finiteOmega d) ∨
    (((∑ v, g.deficit v) + graphExcess g.graph ≤ finiteOmega d + 1) ∧ ∃ v, 0 < g.deficit v)

omit [DecidableEq V] in
theorem FiniteReferenceBudget.complexity_le {g : DeficientGraph V d} (h : g.FiniteReferenceBudget) :
    (∑ v, g.deficit v) + graphExcess g.graph ≤ finiteOmega d + 1 := by
  rcases h with h | ⟨h, _⟩ <;> omega

theorem finite_class_reference_bounds (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected) (hbudget : g.FiniteReferenceBudget)
    (z : ℂ) (hz : 0 < z.im) :
    (∀ i j, ‖g.extensionGreen (semicircleRoot z) z i j‖ ≤
      finiteExtraReferenceConstant d * g.referenceDecay z i j) ∧
    (∀ i j, |(g.extensionGreen (semicircleRoot z) z i j).im| ≤
      finiteExtraReferenceConstant d * (kestenMcKayTransform d (semicircleRoot z) z).im) := by
  rcases hbudget with h | ⟨h, hpos⟩
  · have hh := finiteOmega_reference_bounds d hd g hG h z hz
    constructor
    · intro i j
      exact (hh.1 i j).trans (mul_le_mul_of_nonneg_right (finiteReferenceConstant_le_extra d hd)
        (g.referenceDecay_pos hd z i j).le)
    · intro i j
      have hmd := (kestenMcKayTransform_im_pos d (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le).le
      exact (hh.2.1 i j).trans (mul_le_mul_of_nonneg_right (finiteReferenceConstant_le_extra d hd) hmd)
  · exact g.finiteOmega_extra_reference_bounds hd hG h hpos z hz

/-- Genuine perturbed-model kernel decay for both source complexity cases. -/
theorem finite_class_kernel_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected) (hbudget : g.FiniteReferenceBudget)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2)
    (i j : V) :
    ‖g.extensionGreen q z i j‖ ≤ 2 * finiteExtraReferenceConstant d * g.referenceDecay z i j := by
  have hω : graphExcess g.graph ≤ finiteOmega d + 1 := by have hh := hbudget.complexity_le; omega
  have hC : 0 ≤ finiteExtraReferenceConstant d :=
    le_trans (by norm_num) (finiteExtraReferenceConstant_ge_one d hd)
  exact (g.reference_boundary_stability hd hG (finiteOmega d + 1) hω z q hz hq
    (finiteExtraReferenceConstant d) hC R hR (g.finite_class_reference_bounds hd hG hbudget z hz).1
    small i j).2

end DeficientGraph
end LocalLaw
