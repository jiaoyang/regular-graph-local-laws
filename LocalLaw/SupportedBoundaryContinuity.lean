import LocalLaw.SupportedSquareRows
import LocalLaw.KernelSquareSum

/-! # Boundary continuity for a switched model without a new reference class -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
namespace DeficientGraph
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] {d : ℕ}

theorem extensionGreen_two_parameter_square_rows (g : DeficientGraph V d) (hd : 3≤d)
    (q v z : ℂ) (hz : 0<z.im) (hq : 0 ≤ q.im) (hv : 0 ≤ v.im)
    (S : ℝ) (i j : V)
    (hrow : ∑ k,‖g.extensionGreen q z i k‖^2≤S)
    (hcol : ∑ k,‖g.extensionGreen v z k j‖^2≤S) :
    ‖g.extensionGreen q z i j-g.extensionGreen v z i j‖≤2*S*‖q-v‖ := by
  let P:=g.extensionGreen q z
  let Q:=g.extensionGreen v z
  have hp:=boundary_product_sum_le (fun k=>P i k) (fun k=>Q k j) S hrow hcol
  have hcoeff (k : V) : ‖(g.boundaryCoefficient k:ℂ)‖≤2 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (g.boundaryCoefficient_nonnegative hd k)]
    exact g.boundaryCoefficient_le_two hd k
  have hmiddle : ‖(P*g.boundaryDiagonal*Q) i j‖≤2*S := by
    change ‖∑ k,(P*g.boundaryDiagonal) i k*Q k j‖≤2*S
    simp only [boundaryDiagonal,Matrix.mul_diagonal]
    calc
      _≤∑ k,‖P i k*(g.boundaryCoefficient k:ℂ)*Q k j‖ := norm_sum_le _ _
      _≤∑ k,2*(‖P i k‖*‖Q k j‖) := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul,norm_mul]
        have hh:=mul_le_mul_of_nonneg_left (hcoeff k) (mul_nonneg (norm_nonneg (P i k)) (norm_nonneg (Q k j)))
        nlinarith only [hh]
      _=2*(∑ k,‖P i k‖*‖Q k j‖) := (Finset.mul_sum ..).symm
      _≤_ := mul_le_mul_of_nonneg_left hp (by norm_num)
  have hid:=boundaryGreen_sub_two_expanded g.H g.boundaryDiagonal q v z z
    (g.extensionMatrix_isUnit hd q z hz hq) (g.extensionMatrix_isUnit hd v z hz hv)
  simp only [sub_self,zero_smul,zero_add] at hid
  have he:=congrArg (fun M : Matrix V V ℂ=>M i j) hid
  change P i j-Q i j=(q-v)*(P*g.boundaryDiagonal*Q) i j at he
  change ‖P i j-Q i j‖≤_
  rw [he,norm_mul]
  exact (mul_le_mul_of_nonneg_left hmiddle (norm_nonneg _)).trans_eq (by ring)

theorem supported_two_parameter_continuity (g h : DeficientGraph V d) (hd : 3≤d)
    (hbudget : g.ComponentFiniteReferenceBudget) (e : I↪V) (q v z : ℂ)
    (hz : 0<z.im) (hq : 0 ≤ q.im) (hv : 0 ≤ v.im)
    (R : ℕ) (hR : ∀ i j,g.graph.dist i j≤R)
    (smallQ : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (smallV : ‖v-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (supportQ : ∀ i j,i∉Set.range e ∨ j∉Set.range e→
      (h.extensionMatrix q z-g.extensionMatrix q z) i j=0)
    (supportV : ∀ i j,i∉Set.range e ∨ j∉Set.range e→
      (h.extensionMatrix v z-g.extensionMatrix v z) i j=0)
    (aq av wq wv : ℝ) (haq : 0≤aq) (hav : 0≤av) (hwq : 0≤wq) (hwv : 0≤wv)
    (massQ : ∀ i,∑ j,‖(h.extensionMatrix q z-g.extensionMatrix q z) (e i) (e j)‖≤wq)
    (massV : ∀ i,∑ j,‖(h.extensionMatrix v z-g.extensionMatrix v z) (e i) (e j)‖≤wv)
    (x y : V) (rowQ : ∑ i,‖h.extensionGreen q z x (e i)‖≤aq)
    (rowV : ∑ i,‖h.extensionGreen v z y (e i)‖≤av) :
    ‖h.extensionGreen q z x y-h.extensionGreen v z x y‖≤
      32*finiteExtraReferenceConstant d^2*(2+(aq*wq)^2+(av*wv)^2)*((R:ℝ)+1)*‖q-v‖ := by
  let S:=8*finiteExtraReferenceConstant d^2*((R:ℝ)+1)
  let SQ:=2*(1+(aq*wq)^2)*S
  let SV:=2*(1+(av*wv)^2)*S
  have hS : 0≤S := by dsimp only [S]; positivity
  have hSQ : 0≤SQ := by dsimp only [SQ]; positivity
  have hSV : 0≤SV := by dsimp only [SV]; positivity
  have hrowsQ:=inverse_supported_square_row (g.extensionMatrix q z) (h.extensionMatrix q z)
    (g.extensionMatrix_isUnit hd q z hz hq) (h.extensionMatrix_isUnit hd q z hz hq)
    e supportQ aq wq S haq hwq hS x
    (fun i=>g.componentwise_extensionGreen_square_sum hd hbudget z q hz hq R hR smallQ i) rowQ massQ
  have hrowsV:=inverse_supported_square_row (g.extensionMatrix v z) (h.extensionMatrix v z)
    (g.extensionMatrix_isUnit hd v z hz hv) (h.extensionMatrix_isUnit hd v z hz hv)
    e supportV av wv S hav hwv hS y
    (fun i=>g.componentwise_extensionGreen_square_sum hd hbudget z v hz hv R hR smallV i) rowV massV
  have hrow : ∑ k,‖h.extensionGreen q z x k‖^2≤SQ+SV := hrowsQ.trans (le_add_of_nonneg_right hSV)
  have hcol : ∑ k,‖h.extensionGreen v z k y‖^2≤SQ+SV := by
    have hs:=h.extensionGreen_isSymm v z
    have hh : (∑ k,‖h.extensionGreen v z k y‖^2)=(∑ k,‖h.extensionGreen v z y k‖^2) :=
      Finset.sum_congr rfl (fun k _=>congrArg (fun a : ℂ=>‖a‖^2) (hs.apply y k))
    rw [hh]
    exact hrowsV.trans (le_add_of_nonneg_left hSQ)
  exact (h.extensionGreen_two_parameter_square_rows hd q v z hz hq hv (SQ+SV) x y hrow hcol).trans_eq
    (by dsimp only [SQ,SV,S]; ring)

end DeficientGraph
end LocalLaw
