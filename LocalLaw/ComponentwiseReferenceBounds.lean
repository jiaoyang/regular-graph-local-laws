import LocalLaw.ComponentModel

/-!
# Actual componentwise source reference estimates

Disconnected finite models are estimated on their genuine inverse blocks.
Each component has its own proved deficit/excess budget. Cross-component
entries vanish, so no connectedness or total-complexity assumption is imposed
on the full model.
-/

set_option maxHeartbeats 1400000

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance componentwiseDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
local instance (priority := high) canonicalComponentwiseMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

/-- Each actual connected component lies in the base finite reference class. -/
def ComponentReferenceBudget (g : DeficientGraph V d) : Prop :=
  ∀ c : g.graph.ConnectedComponent,
    (∑ v, (g.restrict c.supp).deficit v) + graphExcess (g.restrict c.supp).graph ≤ finiteOmega d

/-- The disconnected physical reference model has a uniform entry cap. -/
theorem componentwise_reference_entry_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hbudget : g.ComponentReferenceBudget) (z : ℂ) (hz : 0 < z.im) (i j : V) :
    ‖g.extensionGreen (semicircleRoot z) z i j‖ ≤ finiteReferenceConstant d := by
  let c := g.graph.connectedComponentMk i
  have hi : i ∈ c.supp := rfl
  have hC : 0 ≤ finiteReferenceConstant d := le_trans (by norm_num) (finiteReferenceConstant_ge_one d hd)
  by_cases hj : j ∈ c.supp
  · have hconn : (g.restrict c.supp).graph.Connected := c.connected_induce_supp
    have hh := (finiteOmega_reference_bounds d hd (g.restrict c.supp) hconn (hbudget c) z hz).1
      ⟨i, hi⟩ ⟨j, hj⟩
    rw [g.component_extensionGreen hd c c.supp rfl (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le] at hh
    simp only [Matrix.submatrix_apply] at hh
    have hs := physicalTransfer_sq_le_half d hd z
    have ht : ‖-semicircleRoot z * treeEdgeWeight d‖ ≤ 1 := by
      dsimp only [physicalTransfer] at hs
      nlinarith [norm_nonneg (-semicircleRoot z * treeEdgeWeight d)]
    exact hh.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) ht) hC)
  · rw [g.extensionGreen_zero_across_cut hd c.supp (g.component_cut c)
      (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le i hi j hj, norm_zero]
    exact hC

/-- The actual reference-imaginary cap holds blockwise as well. -/
theorem componentwise_reference_im_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hbudget : g.ComponentReferenceBudget) (z : ℂ) (hz : 0 < z.im) (i j : V) :
    |(g.extensionGreen (semicircleRoot z) z i j).im| ≤
      finiteReferenceConstant d * (kestenMcKayTransform d (semicircleRoot z) z).im := by
  let c := g.graph.connectedComponentMk i
  have hi : i ∈ c.supp := rfl
  by_cases hj : j ∈ c.supp
  · have hconn : (g.restrict c.supp).graph.Connected := c.connected_induce_supp
    have hh := (finiteOmega_reference_bounds d hd (g.restrict c.supp) hconn (hbudget c) z hz).2.1
      ⟨i, hi⟩ ⟨j, hj⟩
    rw [g.component_extensionGreen hd c c.supp rfl (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le] at hh
    exact hh
  · rw [g.extensionGreen_zero_across_cut hd c.supp (g.component_cut c)
      (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le i hi j hj, Complex.zero_im, abs_zero]
    have hC := finiteReferenceConstant_ge_one d hd
    have hm := (kestenMcKayTransform_im_pos d (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le).le
    positivity

/-- Bounded-domain diagonal comparability is inherited by each true block. -/
theorem componentwise_reference_diagonal_bounds (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hbudget : g.ComponentReferenceBudget) (z : ℂ) (hz : 0 < z.im)
    (B : ℝ) (hB : ‖z‖ ≤ B) (i : V) :
    1 / (finiteReferenceConstant d * (B + 2)) ≤ ‖g.extensionGreen (semicircleRoot z) z i i‖ ∧
      ‖g.extensionGreen (semicircleRoot z) z i i‖ ≤ finiteReferenceConstant d := by
  let c := g.graph.connectedComponentMk i
  have hi : i ∈ c.supp := rfl
  have hconn : (g.restrict c.supp).graph.Connected := c.connected_induce_supp
  have hh := finiteOmega_reference_diagonal_bounds d hd (g.restrict c.supp) hconn (hbudget c)
    z hz B hB ⟨i, hi⟩
  rw [g.component_extensionGreen hd c c.supp rfl (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le] at hh
  exact hh

/-- The actual global boundary correction needs only componentwise budgets. -/
theorem componentwise_boundary_uniform_stability (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hbudget : g.ComponentReferenceBudget) (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * ((R : ℝ) + 1) ≤ 1 / 2) (i j : V) :
    ‖g.extensionGreen q z i j - g.extensionGreen (semicircleRoot z) z i j‖ ≤
      (8 * finiteReferenceConstant d ^ 2 * coreConvolutionConstant (finiteOmega d)) * ‖q - semicircleRoot z‖ := by
  let c := g.graph.connectedComponentMk i
  have hi : i ∈ c.supp := rfl
  by_cases hj : j ∈ c.supp
  · exact g.isolated_finiteOmega_boundary_uniform_stability hd c.supp (g.component_cut c)
      c.connected_induce_supp (hbudget c) z q hz hq R hR small ⟨i, hi⟩ ⟨j, hj⟩
  · rw [g.extensionGreen_zero_across_cut hd c.supp (g.component_cut c) q z hz hq i hi j hj,
      g.extensionGreen_zero_across_cut hd c.supp (g.component_cut c) (semicircleRoot z) z hz
        (semicircleRoot_im_pos hz).le i hi j hj, sub_self, norm_zero]
    unfold coreConvolutionConstant
    positivity

/-- Uniform perturbed entry caps now follow from genuine reference and
boundary correction estimates in every component. -/
theorem componentwise_perturbed_entry_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hbudget : g.ComponentReferenceBudget) (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * ((R : ℝ) + 1) ≤ 1 / 2) (i j : V) :
    ‖g.extensionGreen q z i j‖ ≤ finiteReferenceConstant d +
      (8 * finiteReferenceConstant d ^ 2 * coreConvolutionConstant (finiteOmega d)) * ‖q - semicircleRoot z‖ := by
  have hh := norm_add_le (g.extensionGreen (semicircleRoot z) z i j)
    (g.extensionGreen q z i j - g.extensionGreen (semicircleRoot z) z i j)
  rw [add_sub_cancel] at hh
  exact hh.trans (add_le_add (g.componentwise_reference_entry_bound hd hbudget z hz i j)
    (g.componentwise_boundary_uniform_stability hd hbudget z q hz hq R hR small i j))

end DeficientGraph
end
end LocalLaw
