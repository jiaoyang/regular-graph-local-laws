import LocalLaw.ComponentwiseReferenceBounds
import LocalLaw.BoundarySchurRows

/-!
# Actual perturbed kernel decay in disconnected models

The constructed reference budget is applied on the actual component inverse
block. Across different components the inverse vanishes. No decay estimate
is imposed as an additional hypothesis.
-/

noncomputable section
namespace LocalLaw
local instance componentDecayDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) canonicalComponentDecayMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem componentwise_perturbed_kernel_decay (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hbudget : g.ComponentReferenceBudget) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * ((R : ℝ) + 1) ≤ 1 / 2) (i j : V) :
    ‖g.extensionGreen q z i j‖ ≤
      2 * finiteReferenceConstant d * physicalTransfer d z ^ g.graph.dist i j := by
  let c := g.graph.connectedComponentMk i
  let gc := g.restrict c.supp
  have hC : 0 ≤ finiteReferenceConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans
    (finiteReferenceConstant_ge_one d hd)
  by_cases hj : j ∈ c.supp
  · have hconn : gc.graph.Connected := c.connected_induce_supp
    have hcomp := hbudget c
    have hω : graphExcess gc.graph ≤ finiteOmega d := by
      change (∑ v, gc.deficit v) + graphExcess gc.graph ≤ finiteOmega d at hcomp
      omega
    have hdiam : ∀ a b, gc.graph.dist a b ≤ R := by
      intro a b
      change (g.graph.induce c.supp).dist a b ≤ R
      rw [isolated_induce_distance g.graph c.supp (g.component_cut c)]
      exact hR a.val b.val
    have href := (finiteOmega_reference_bounds d hd gc hconn hcomp z hz).1
    have hh := (gc.reference_boundary_stability hd hconn (finiteOmega d) hω z q hz hq
      (finiteReferenceConstant d) hC R hdiam href small ⟨i, rfl⟩ ⟨j, hj⟩).2
    rw [g.restrict_extensionGreen_of_isolated hd c.supp (g.component_cut c) q z hz hq] at hh
    simp only [Matrix.submatrix_apply, referenceDecay] at hh
    change ‖g.extensionGreen q z i j‖ ≤ 2 * finiteReferenceConstant d * physicalTransfer d z ^
      (g.graph.induce c.supp).dist ⟨i, rfl⟩ ⟨j, hj⟩ at hh
    rw [isolated_induce_distance g.graph c.supp (g.component_cut c)] at hh
    exact hh
  · rw [g.extensionGreen_zero_across_cut hd c.supp (g.component_cut c) q z hz hq i rfl j hj,
      norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hC) (pow_nonneg (norm_nonneg _) _)

end DeficientGraph
end LocalLaw
