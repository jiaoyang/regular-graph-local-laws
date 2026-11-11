import LocalLaw.ComponentFiniteLocalization

/-! Uniform boundary Lipschitz bounds on the actual componentwise class. -/
noncomputable section
namespace LocalLaw
local instance componentFiniteLipschitzDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) componentFiniteLipschitzMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem componentwise_finite_uniform_lipschitz (g : DeficientGraph V d) (hd : 3≤d)
    (hbudget : g.ComponentFiniteReferenceBudget) (z q v : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (hv : 0≤v.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j≤R)
    (smallq : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (smallv : ‖v-semicircleRoot z‖*finiteExtraReferenceConstant d*coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (i j : V) :
    ‖g.extensionGreen q z i j-g.extensionGreen v z i j‖≤
      (16*finiteExtraReferenceConstant d^2*coreConvolutionConstant (finiteOmega d+1))*‖q-v‖ := by
  let c:=g.graph.connectedComponentMk i
  let gc:=g.restrict c.supp
  have hC : 0≤finiteExtraReferenceConstant d := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  by_cases hj : j∈c.supp
  · have hconn : gc.graph.Connected := c.connected_induce_supp
    have hω : graphExcess gc.graph≤finiteOmega d+1 := by
      change graphExcess (g.restrict c.supp).graph≤finiteOmega d+1
      have hh:=(hbudget c).complexity_le
      omega
    have hdiam : ∀ a b, gc.graph.dist a b≤R := by
      intro a b
      change (g.graph.induce c.supp).dist a b≤R
      rw [isolated_induce_distance g.graph c.supp (g.component_cut c)]
      exact hR a.val b.val
    have hh:=gc.reference_boundary_uniform_lipschitz hd hconn (finiteOmega d+1) hω z q v hz hq hv
      (finiteExtraReferenceConstant d) hC R hdiam (gc.finite_class_reference_bounds hd hconn (hbudget c) z hz).1
      smallq smallv ⟨i,rfl⟩ ⟨j,hj⟩
    rw [g.restrict_extensionGreen_of_isolated hd c.supp (g.component_cut c) q z hz hq,
      g.restrict_extensionGreen_of_isolated hd c.supp (g.component_cut c) v z hz hv] at hh
    simpa only [Matrix.submatrix_apply,dist_eq_norm] using hh
  · rw [g.extensionGreen_zero_across_cut hd c.supp (g.component_cut c) q z hz hq i rfl j hj,
      g.extensionGreen_zero_across_cut hd c.supp (g.component_cut c) v z hz hv i rfl j hj,sub_self,norm_zero]
    have hCo:=coreConvolutionConstant_nonnegative (finiteOmega d+1)
    positivity

end DeficientGraph
end LocalLaw
