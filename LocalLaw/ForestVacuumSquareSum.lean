import LocalLaw.ForestVacuumResidual
import LocalLaw.KernelSquareSum

/-! # Square sums and residual bounds for formal forest reference columns -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance forestVacuumSquareDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) forestVacuumComponentMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _
variable {V : Type} [Fintype V] [DecidableEq V]

theorem formalForestKernel_square_sum (G : SimpleGraph V) (d : ℕ) (hd : 3≤d)
    (hdeg : ∀ v,G.degree v≤d) (q p : ℂ) (R : ℕ) (hR : ∀ i j,G.dist i j≤R)
    (P Q : ℝ) (hP : 0≤P) (_hQ : 0≤Q) (hp : ‖p‖≤P)
    (hq : ∀ n≤R,‖q‖^n≤Q) (j : V) :
    (∑ i,‖formalForestKernel G d q p i j‖^2)≤2*(P*Q)^2*((R:ℝ)+1) := by
  let c := G.connectedComponentMk j
  let H := G.induce c.supp
  let jj : c.supp := ⟨j,rfl⟩
  have hconn : H.Connected := c.connected_induce_supp
  have hdegH (v : c.supp) : H.degree v≤d := (induced_degree_le G c.supp v).trans (hdeg v.val)
  have hdist (u v : c.supp) : H.dist u v=G.dist u.val v.val :=
    isolated_induce_distance G c.supp (fun a ha b hb hab => by
      exact hb ((SimpleGraph.ConnectedComponent.sound hab.reachable).symm.trans ha)) u v
  have hentry (i : c.supp) :
      ‖formalForestKernel G d q p i.val j‖^2≤
        (P*Q)^2*(((d:ℝ)-1)^H.dist jj i)⁻¹ := by
    have hr : G.Reachable i.val j := SimpleGraph.ConnectedComponent.exact i.property
    have hn : G.dist i.val j≤R := hR _ _
    have hpower := mul_le_mul hp (hq _ hn) (pow_nonneg (norm_nonneg q) _) hP
    have hh := mul_le_mul_of_nonneg_right hpower
      (pow_nonneg (norm_nonneg (treeEdgeWeight d)) (G.dist i.val j))
    have heq : ‖formalForestKernel G d q p i.val j‖=
        (‖p‖*‖q‖^G.dist i.val j)*‖treeEdgeWeight d‖^G.dist i.val j := by
      simp only [formalForestKernel,forestKernelColumn,if_pos hr,norm_mul,norm_pow,norm_neg,mul_pow]
      ring
    rw [←heq] at hh
    have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
    rw [mul_pow,←pow_mul, Nat.mul_comm (G.dist i.val j) 2,pow_mul,
      treeEdgeWeight_norm_sq d hd,one_div,inv_pow] at hs
    rw [hdist]
    change _≤(P*Q)^2*(((d:ℝ)-1)^G.dist j i.val)⁻¹
    rw [SimpleGraph.dist_comm]
    exact hs
  have hsum := connected_critical_square_kernel_sum H hconn d hd hdegH jj R
    (fun i => by rw [hdist]; exact hR _ _)
  have hsub : (∑ i : c.supp,‖formalForestKernel G d q p i.val j‖^2)≤
      2*(P*Q)^2*((R:ℝ)+1) := by
    calc
      _ ≤ ∑ i : c.supp,(P*Q)^2*(((d:ℝ)-1)^H.dist jj i)⁻¹ :=
        Finset.sum_le_sum (fun i _ => hentry i)
      _ = (P*Q)^2*(∑ i : c.supp,(((d:ℝ)-1)^H.dist jj i)⁻¹) := (Finset.mul_sum ..).symm
      _ ≤ (P*Q)^2*(2*((R:ℝ)+1)) := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = _ := by ring
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i : V => i∈c.supp)
    (fun i => ‖formalForestKernel G d q p i j‖^2)
  have hz : (∑ i : {i : V // i∉c.supp},‖formalForestKernel G d q p i.val j‖^2)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hr : ¬G.Reachable i.val j := fun h => i.property (SimpleGraph.ConnectedComponent.sound h)
    simp only [formalForestKernel,forestKernelColumn,if_neg hr,norm_zero,zero_pow (by decide : 2≠0)]
  rw [hz,add_zero] at hsplit
  exact hsplit ▸ hsub

namespace DeficientGraph
variable {d : ℕ}

theorem formal_forest_error_of_finite_class (g : DeficientGraph V d) (hd : 3≤d)
    (hbudget : g.ComponentFiniteReferenceBudget) (hzero : ∀ v,g.deficit v=0)
    (hforest : g.graph.IsAcyclic) (q p z : ℂ) (hq : q≠0)
    (hp : p*(q⁻¹-q/((d:ℂ)-1))=1) (hz : 0<z.im) (hqim : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j,g.graph.dist i j≤R)
    (small : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (P Q : ℝ) (hP : 0≤P) (hQ : 0≤Q) (hpbound : ‖p‖≤P)
    (hqpow : ∀ n≤R,‖q‖^n≤Q) (i j : V) :
    ‖g.extensionGreen q z i j-formalForestKernel g.graph d q p i j‖≤
      ‖(1+z*q+q^2)/q‖*(8*finiteExtraReferenceConstant d^2+2*(P*Q)^2)*((R:ℝ)+1) := by
  let S := (8*finiteExtraReferenceConstant d^2+2*(P*Q)^2)*((R:ℝ)+1)
  have hRpos : 0≤(R:ℝ)+1 := by positivity
  have hrow := g.componentwise_extensionGreen_square_sum hd hbudget z q hz hqim R hR small i
  have hcol := formalForestKernel_square_sum g.graph d hd g.degree_le q p R hR P Q hP hQ hpbound hqpow j
  have hrow' : (∑ k,‖g.extensionGreen q z i k‖^2)≤S := hrow.trans (by dsimp [S]; nlinarith [sq_nonneg (P*Q)])
  have hcol' : (∑ k,‖formalForestKernel g.graph d q p k j‖^2)≤S := hcol.trans (by dsimp [S]; nlinarith [sq_nonneg (finiteExtraReferenceConstant d)])
  exact (g.extensionGreen_formal_forest_error hd hzero hforest q p z hq hp hz hqim S i j hrow' hcol').trans_eq (by dsimp [S]; ring)

end DeficientGraph
end LocalLaw
