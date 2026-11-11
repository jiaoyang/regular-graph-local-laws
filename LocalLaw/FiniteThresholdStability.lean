import LocalLaw.BoundedExcessStability
import LocalLaw.FiniteReferenceThreshold
import LocalLaw.ExtraDeficitReference

/-!
# Finite-threshold boundary sensitivity without reference hypotheses

The degree-dependent positive maximal finite reference threshold is constructed
in `FiniteReferenceThreshold`. Here it supplies the reference estimates to the
actual bounded-excess perturbation theorem. This is a finite-model result;
it does not identify the threshold with a class of infinite operators.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
namespace DeficientGraph

variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

/-- Actual connected models at the constructed maximal finite threshold have
uniform boundary sensitivity, without a reference-class or convolution input. -/
theorem finiteOmega_boundary_uniform_stability (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected)
    (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ finiteOmega d)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * ((R : ℝ) + 1) ≤ 1 / 2)
    (i j : V) :
    ‖g.extensionGreen q z i j - g.extensionGreen (semicircleRoot z) z i j‖ ≤
      (8 * finiteReferenceConstant d ^ 2 * coreConvolutionConstant (finiteOmega d)) *
        ‖q - semicircleRoot z‖ := by
  have hω : graphExcess g.graph ≤ finiteOmega d := by omega
  have hC : 0 ≤ finiteReferenceConstant d := le_trans (by norm_num) (finiteReferenceConstant_ge_one d hd)
  have href := (finiteOmega_reference_bounds d hd g hG hbudget z hz).1
  exact g.reference_boundary_uniform_stability hd hG (finiteOmega d) hω z q hz hq
    (finiteReferenceConstant d) hC R hR href small i j

/-- The actual physical-reference imaginary estimate and boundary correction
give a concrete diagonal variance cap throughout this finite source class. -/
theorem finiteOmega_boundary_im_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected)
    (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ finiteOmega d)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * ((R : ℝ) + 1) ≤ 1 / 2)
    (i j : V) :
    |(g.extensionGreen q z i j).im| ≤
      finiteReferenceConstant d * (kestenMcKayTransform d (semicircleRoot z) z).im +
        (8 * finiteReferenceConstant d ^ 2 * coreConvolutionConstant (finiteOmega d)) *
          ‖q - semicircleRoot z‖ := by
  have hdiff := g.finiteOmega_boundary_uniform_stability hd hG hbudget z q hz hq R hR small i j
  have href := (finiteOmega_reference_bounds d hd g hG hbudget z hz).2.1 i j
  have him := Complex.abs_im_le_norm (g.extensionGreen q z i j -
    g.extensionGreen (semicircleRoot z) z i j)
  have hsplit := abs_add_le ((g.extensionGreen q z i j).im -
    (g.extensionGreen (semicircleRoot z) z i j).im)
    (g.extensionGreen (semicircleRoot z) z i j).im
  rw [sub_add_cancel] at hsplit
  simp only [Complex.sub_im] at him
  linarith

/-- Two perturbed boundary parameters satisfy a degree-dependent uniform
Lipschitz bound at the constructed finite threshold. -/
theorem finiteOmega_boundary_uniform_lipschitz (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected)
    (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ finiteOmega d)
    (z q v : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (hv : 0 ≤ v.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (smallq : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * ((R : ℝ) + 1) ≤ 1 / 2)
    (smallv : ‖v - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * ((R : ℝ) + 1) ≤ 1 / 2)
    (i j : V) :
    ‖g.extensionGreen q z i j - g.extensionGreen v z i j‖ ≤
      (16 * finiteReferenceConstant d ^ 2 * coreConvolutionConstant (finiteOmega d)) * dist q v := by
  have hω : graphExcess g.graph ≤ finiteOmega d := by omega
  have hC : 0 ≤ finiteReferenceConstant d := le_trans (by norm_num) (finiteReferenceConstant_ge_one d hd)
  have href := (finiteOmega_reference_bounds d hd g hG hbudget z hz).1
  exact g.reference_boundary_uniform_lipschitz hd hG (finiteOmega d) hω z q v hz hq hv
    (finiteReferenceConstant d) hC R hR href smallq smallv i j

/-- A positive deficit permits one additional unit of complexity, using
the proved leaf-augmentation comparison for the actual reference inverse. -/
theorem finiteOmega_extra_boundary_uniform_stability (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected)
    (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ finiteOmega d + 1)
    (hpositive : ∃ v, 0 < g.deficit v)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2)
    (i j : V) :
    ‖g.extensionGreen q z i j - g.extensionGreen (semicircleRoot z) z i j‖ ≤
      (8 * finiteExtraReferenceConstant d ^ 2 * coreConvolutionConstant (finiteOmega d + 1)) *
        ‖q - semicircleRoot z‖ := by
  have hω : graphExcess g.graph ≤ finiteOmega d + 1 := by omega
  have hC : 0 ≤ finiteExtraReferenceConstant d :=
    le_trans (by norm_num) (finiteExtraReferenceConstant_ge_one d hd)
  have href := (g.finiteOmega_extra_reference_bounds hd hG hbudget hpositive z hz).1
  exact g.reference_boundary_uniform_stability hd hG (finiteOmega d + 1) hω z q hz hq
    (finiteExtraReferenceConstant d) hC R hR href small i j

/-- The extra-deficit model has a derived reference-imaginary cap plus its
actual boundary correction; no observation-variance bound is assumed. -/
theorem finiteOmega_extra_boundary_im_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected)
    (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ finiteOmega d + 1)
    (hpositive : ∃ v, 0 < g.deficit v)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2)
    (i j : V) :
    |(g.extensionGreen q z i j).im| ≤
      finiteExtraReferenceConstant d * (kestenMcKayTransform d (semicircleRoot z) z).im +
        (8 * finiteExtraReferenceConstant d ^ 2 * coreConvolutionConstant (finiteOmega d + 1)) *
          ‖q - semicircleRoot z‖ := by
  have hdiff := g.finiteOmega_extra_boundary_uniform_stability hd hG hbudget hpositive z q hz hq R hR small i j
  have href := (g.finiteOmega_extra_reference_bounds hd hG hbudget hpositive z hz).2 i j
  have him := Complex.abs_im_le_norm (g.extensionGreen q z i j -
    g.extensionGreen (semicircleRoot z) z i j)
  have hsplit := abs_add_le ((g.extensionGreen q z i j).im -
    (g.extensionGreen (semicircleRoot z) z i j).im)
    (g.extensionGreen (semicircleRoot z) z i j).im
  rw [sub_add_cancel] at hsplit
  simp only [Complex.sub_im] at him
  linarith

theorem finiteOmega_extra_boundary_uniform_lipschitz (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected)
    (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ finiteOmega d + 1)
    (hpositive : ∃ v, 0 < g.deficit v)
    (z q v : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (hv : 0 ≤ v.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (smallq : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2)
    (smallv : ‖v - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2)
    (i j : V) :
    ‖g.extensionGreen q z i j - g.extensionGreen v z i j‖ ≤
      (16 * finiteExtraReferenceConstant d ^ 2 * coreConvolutionConstant (finiteOmega d + 1)) * dist q v := by
  have hω : graphExcess g.graph ≤ finiteOmega d + 1 := by omega
  have hC : 0 ≤ finiteExtraReferenceConstant d :=
    le_trans (by norm_num) (finiteExtraReferenceConstant_ge_one d hd)
  have href := (g.finiteOmega_extra_reference_bounds hd hG hbudget hpositive z hz).1
  exact g.reference_boundary_uniform_lipschitz hd hG (finiteOmega d + 1) hω z q v hz hq hv
    (finiteExtraReferenceConstant d) hC R hR href smallq smallv i j

end DeficientGraph
end LocalLaw
