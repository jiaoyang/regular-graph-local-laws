import LocalLaw.ZeroDeficitForestReference
import LocalLaw.BoundaryResolvent

/-! # Formal forest columns with their exact self-consistency residual

The boundary parameter need not solve the semicircle equation. Its defect
appears as a scalar spectral shift, which costs the product of two square
sums instead of a first-order boundary-parameter error.
-/

open scoped BigOperators Matrix
noncomputable section
namespace LocalLaw
local instance forestVacuumResidualDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def formalForestKernel {V : Type*} (G : SimpleGraph V) (d : ℕ) (q p : ℂ) : Matrix V V ℂ :=
  fun i j => forestKernelColumn G j p (-q*treeEdgeWeight d) i

namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

theorem extensionMatrix_formal_forest_residual (g : DeficientGraph V d) (hd : 3≤d)
    (hzero : ∀ v,g.deficit v=0) (hforest : g.graph.IsAcyclic) (q p z : ℂ)
    (hq : q≠0) (hp : p*(q⁻¹-q/((d:ℂ)-1))=1) :
    g.extensionMatrix q z*formalForestKernel g.graph d q p=
      1-((1+z*q+q^2)/q) • formalForestKernel g.graph d q p := by
  let w : ℂ := -q-q⁻¹
  have hqeq : q^2+w*q+1=0 := by dsimp [w]; field_simp only [hq]; ring
  have hk : (d:ℂ)-1≠0 := by
    have h : (3:ℝ)≤d := Nat.cast_le.mpr hd
    intro he
    have hh := congrArg Complex.re he
    simp only [Complex.sub_re,Complex.natCast_re,Complex.one_re,Complex.zero_re] at hh
    linarith
  have hp' : p*(-w-((d:ℂ)-0)*q/((d:ℂ)-1))=1 := by
    calc
      _ = p*(q⁻¹-q/((d:ℂ)-1)) := by dsimp [w]; field_simp only [hk]; ring
      _ = 1 := hp
  ext i j
  have hcol := forestReferenceMatrix_column g.graph hforest d hd j 0 q w p hqeq
  simp only [Nat.cast_zero] at hcol
  rw [hp'] at hcol
  have hM : g.extensionMatrix q z=
      forestReferenceMatrix g.graph d j 0 q w+(w-z) • (1:Matrix V V ℂ) := by
    rw [←g.extensionMatrix_zero_deficit_forest_form hzero j q w]
    ext a b
    simp only [extensionMatrix,boundaryMatrix,spectralMatrix,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,
      smul_eq_mul,Matrix.one_apply]
    split_ifs <;> ring
  have hentry := congrFun hcol i
  have he : w-z= -((1+z*q+q^2)/q) := by dsimp [w]; field_simp only [hq]; ring
  change (g.extensionMatrix q z*ᵥ forestKernelColumn g.graph j p (-q*treeEdgeWeight d)) i=_
  rw [hM,Matrix.add_mulVec,Matrix.smul_mulVec_assoc,Matrix.one_mulVec]
  rw [Pi.add_apply,hentry,he]
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,formalForestKernel,
    Pi.smul_apply,Pi.single_apply,Matrix.one_apply]
  split_ifs <;> ring

theorem extensionGreen_formal_forest_difference (g : DeficientGraph V d) (hd : 3≤d)
    (hzero : ∀ v,g.deficit v=0) (hforest : g.graph.IsAcyclic) (q p z : ℂ)
    (hq : q≠0) (hp : p*(q⁻¹-q/((d:ℂ)-1))=1) (hz : 0<z.im) (hqim : 0 ≤ q.im) :
    g.extensionGreen q z-formalForestKernel g.graph d q p=
      ((1+z*q+q^2)/q) • (g.extensionGreen q z*formalForestKernel g.graph d q p) := by
  have hr := g.extensionMatrix_formal_forest_residual hd hzero hforest q p z hq hp
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp (g.extensionMatrix_isUnit hd q z hz hqim)
  have hh := congrArg (fun A : Matrix V V ℂ => g.extensionGreen q z*A) hr
  dsimp only at hh
  rw [←Matrix.mul_assoc] at hh
  change (g.extensionMatrix q z)⁻¹*g.extensionMatrix q z*formalForestKernel g.graph d q p=_ at hh
  rw [Matrix.nonsing_inv_mul _ hu,Matrix.one_mul,Matrix.mul_sub,Matrix.mul_one,
    Matrix.mul_smul] at hh
  exact sub_eq_iff_eq_add.mpr ((eq_sub_iff_add_eq.mp hh).symm.trans (add_comm _ _))

theorem extensionGreen_formal_forest_error (g : DeficientGraph V d) (hd : 3≤d)
    (hzero : ∀ v,g.deficit v=0) (hforest : g.graph.IsAcyclic) (q p z : ℂ)
    (hq : q≠0) (hp : p*(q⁻¹-q/((d:ℂ)-1))=1) (hz : 0<z.im) (hqim : 0 ≤ q.im)
    (S : ℝ) (i j : V)
    (hrow : (∑ k,‖g.extensionGreen q z i k‖^2)≤S)
    (hcol : (∑ k,‖formalForestKernel g.graph d q p k j‖^2)≤S) :
    ‖g.extensionGreen q z i j-formalForestKernel g.graph d q p i j‖≤
      ‖(1+z*q+q^2)/q‖*S := by
  have hh := congrArg (fun A : Matrix V V ℂ => A i j)
    (g.extensionGreen_formal_forest_difference hd hzero hforest q p z hq hp hz hqim)
  change g.extensionGreen q z i j-formalForestKernel g.graph d q p i j=
    ((1+z*q+q^2)/q)*(g.extensionGreen q z*formalForestKernel g.graph d q p) i j at hh
  rw [hh,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  change ‖∑ k,g.extensionGreen q z i k*formalForestKernel g.graph d q p k j‖≤S
  exact (norm_sum_le _ _).trans (by
    simp only [norm_mul]
    exact boundary_product_sum_le _ _ S hrow hcol)

end DeficientGraph
end LocalLaw
