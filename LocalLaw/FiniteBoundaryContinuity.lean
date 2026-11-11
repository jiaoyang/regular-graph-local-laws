import LocalLaw.KernelSquareSum

/-!
# Two-boundary-parameter continuity at the finite reference scale

Both genuine model kernels have their proved squared row bounds. Their
resolvent identity gives a linear-diameter modulus, avoiding the universal
eta^{-2} bound and any unproved uniform boundary convolution.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance finiteBoundaryContinuityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem componentwise_boundary_two_parameter (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hbudget : g.ComponentFiniteReferenceBudget) (u v z : ℂ)
    (hz : 0 < z.im) (hu : 0 ≤ u.im) (hv : 0 ≤ v.im) (R : ℕ)
    (hR : ∀ i j,g.graph.dist i j≤R)
    (smallU : ‖u-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (smallV : ‖v-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2) (i j : V) :
    ‖g.extensionGreen u z i j-g.extensionGreen v z i j‖≤
      16*finiteExtraReferenceConstant d^2*((R:ℝ)+1)*‖u-v‖ := by
  let P := g.extensionGreen u z
  let Q := g.extensionGreen v z
  let S := 8*finiteExtraReferenceConstant d^2*((R:ℝ)+1)
  have hrow : (∑ k,‖P i k‖^2)≤S :=
    g.componentwise_extensionGreen_square_sum hd hbudget z u hz hu R hR smallU i
  have hcol : (∑ k,‖Q k j‖^2)≤S := by
    have hh := g.componentwise_extensionGreen_square_sum hd hbudget z v hz hv R hR smallV j
    have hsym : Q.IsSymm := g.extensionGreen_isSymm v z
    simpa only [hsym.apply] using hh
  have hprod := boundary_product_sum_le (fun k=>P i k) (fun k=>Q k j) S hrow hcol
  have hcoeff (k : V) : ‖(g.boundaryCoefficient k:ℂ)‖≤2 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (g.boundaryCoefficient_nonnegative hd k)]
    exact g.boundaryCoefficient_le_two hd k
  have hmiddle : ‖(P*g.boundaryDiagonal*Q) i j‖≤2*S := by
    change ‖∑ k,(P*g.boundaryDiagonal) i k*Q k j‖≤2*S
    simp only [DeficientGraph.boundaryDiagonal,Matrix.mul_diagonal]
    calc
      _ ≤ ∑ k,‖P i k*(g.boundaryCoefficient k:ℂ)*Q k j‖ := norm_sum_le _ _
      _ ≤ ∑ k,2*(‖P i k‖*‖Q k j‖) := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul,norm_mul]
        nlinarith only [mul_le_mul_of_nonneg_left (hcoeff k) (mul_nonneg (norm_nonneg (P i k)) (norm_nonneg (Q k j)))]
      _ = 2*(∑ k,‖P i k‖*‖Q k j‖) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by norm_num : (0:ℝ)≤2)
  have hid := boundaryGreen_sub_two_expanded g.H g.boundaryDiagonal u v z z
    (g.extensionMatrix_isUnit hd u z hz hu) (g.extensionMatrix_isUnit hd v z hz hv)
  simp only [sub_self,zero_smul,zero_add] at hid
  have he := congrArg (fun A : Matrix V V ℂ=>A i j) hid
  change P i j-Q i j=(u-v)*(P*g.boundaryDiagonal*Q) i j at he
  change ‖P i j-Q i j‖≤_
  rw [he,norm_mul]
  exact (mul_le_mul_of_nonneg_left hmiddle (norm_nonneg _)).trans_eq (by dsimp only [S]; ring)

end DeficientGraph
end LocalLaw
