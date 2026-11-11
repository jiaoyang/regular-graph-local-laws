import LocalLaw.ClosedOutsideBallKernelSum
import LocalLaw.ActualBoundaryRowBudgets
import LocalLaw.OutsideBallReferenceRows

/-! # Logarithmic columns between inner boundary vertices

The target is on the inner boundary, so the critical kernel sum over the
retained ball is linear in its radius. Repeated boundary labels are counted
by their actual degree-bounded fibers.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance boundaryInnerColumnsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def boundaryInnerColumnConstant (d : ℕ) : ℝ :=
  2*finiteExtraReferenceConstant d*(d:ℝ)*(1+8*(d:ℝ))*
    (2*(2*(finiteOmega d:ℝ)+2)*(2*(finiteOmega d:ℝ)+1))

namespace RegularGraph
variable {N d : ℕ}

theorem boundary_model_inner_columns (g : RegularGraph N d) (hd : 3≤d)
    (S : Set (Fin N)) (hconn : (g.deficient.restrict S).graph.Connected)
    (hbudget : (g.deficient.restrict S).ComponentFiniteReferenceBudget)
    (hexcess : graphExcess (g.deficient.restrict S).graph≤finiteOmega d)
    (o : Fin N) (ell : ℕ) (hS : graphBallVertices g.graph o ell⊆S)
    (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (R : ℕ)
    (hR : ∀ u v,(g.deficient.restrict S).graph.dist u v≤R)
    (small : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2) :
    let K := (g.deficient.restrict S).extensionGreen q z
    let l := inducedBoundaryInner g.graph o ell S hS
    ∀ β,∑ α,‖K (l α) (l β)‖≤boundaryInnerColumnConstant d*((ell:ℝ)+1) := by
  dsimp only
  let model := g.deficient.restrict S
  let K := model.extensionGreen q z
  let l := inducedBoundaryInner g.graph o ell S hS
  let root : S := ⟨o,hS (center_mem_graphBall g.graph o ell)⟩
  let C := finiteExtraReferenceConstant d
  let t := (Real.sqrt ((d:ℝ)-1))⁻¹
  have hC : 0≤C := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have ht : 0≤t := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have htransfer : physicalTransfer d z≤t := physicalTransfer_le_critical d z
  have hfiber := inducedBoundaryInner_fiber_bound g.graph o ell S hS d (fun v => (g.regular v).le)
  intro β
  let f : S → ℝ := fun v => if model.graph.dist root v≤ell then t^model.graph.dist (l β) v else 0
  have hf : ∀ v,0≤f v := by intro v; dsimp only [f]; split_ifs <;> positivity
  have hdepth (α) : model.graph.dist root (l α)=ell :=
    induced_boundary_inner_distance g.graph o ell S hS α
  have hpoint (α) : ‖K (l α) (l β)‖≤2*C*f (l α) := by
    have hh := model.componentwise_finite_kernel_decay hd hbudget q z hz hq R hR small (l β) (l α)
    have hsym : K.IsSymm := model.extensionGreen_isSymm q z
    rw [hsym.apply (l β) (l α)]
    apply hh.trans
    dsimp only [f]
    rw [hdepth α,if_pos le_rfl]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (physicalTransfer_pos d hd z).le htransfer _) (by positivity)
  have hsum := outside_ball_critical_kernel_sum_le model.graph hconn d hd model.degree_le
    (finiteOmega d) hexcess root (l β) ell (by rw [hdepth β])
  calc
    _ ≤ ∑ α,2*C*f (l α) := Finset.sum_le_sum (fun α _ => hpoint α)
    _ = 2*C*(∑ α,f (l α)) := (Finset.mul_sum ..).symm
    _ ≤ 2*C*((d:ℝ)*(∑ v,f v)) := mul_le_mul_of_nonneg_left
      (finite_fiber_nonnegative_sum_bound l d hfiber f hf) (by positivity)
    _ ≤ 2*C*((d:ℝ)*((1+8*(d:ℝ))*(2*(2*(finiteOmega d:ℝ)+2)*(2*(finiteOmega d:ℝ)+1))*((ell:ℝ)+1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg d)) (by positivity)
    _ = _ := by dsimp only [C,boundaryInnerColumnConstant]; ring

end RegularGraph
end LocalLaw
