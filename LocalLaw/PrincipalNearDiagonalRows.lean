import LocalLaw.NearDiagonalInverse

/-! # Every principal sampled block inherits inverse row bounds

A bounded full inverse and small off-diagonals first give genuine scalar
pivot reciprocals. The own-diagonal inverse contraction then applies to
any actual principal block, rather than assuming monotonicity of inverse
row sums under restriction.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance principalNearDiagonalDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {I:Type} [Fintype I] [DecidableEq I]

theorem diagonal_pivots_of_inverse_columns (A:Matrix I I ℂ)(hA:IsUnit A)
    (C δ:ℝ)(hC:0≤C)(hδ:0≤δ)
    (hcol:∀i,∑j,‖A⁻¹ j i‖≤C)(hoff:∀i j,i≠j→‖A i j‖≤δ)
    (hsmall:δ*C≤1/2) :
    ∀i,A i i≠0 ∧ ‖(A i i)⁻¹‖≤2*C := by
  classical
  intro i
  have hInv:∀j,‖A⁻¹ j i‖≤C:=fun j=>
    (Finset.single_le_sum (fun k _=>norm_nonneg (A⁻¹ k i)) (Finset.mem_univ j)).trans (hcol i)
  have hp (j:I):‖A i j*A⁻¹ j i‖≤(if j=i then ‖A i i‖*C else 0)+δ*‖A⁻¹ j i‖:=by
    rw [norm_mul]
    by_cases hj:j=i
    · subst j
      simp only [if_true]
      exact (mul_le_mul_of_nonneg_left (hInv i) (norm_nonneg _)).trans
        (le_add_of_nonneg_right (mul_nonneg hδ (norm_nonneg _)))
    · simp only [if_neg hj,zero_add]
      exact mul_le_mul_of_nonneg_right (hoff i j (Ne.symm hj)) (norm_nonneg _)
  have he:(∑j,A i j*A⁻¹ j i)=1:=by
    have hh:=congrArg (fun M:Matrix I I ℂ=>M i i)
      (Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA))
    simpa only [Matrix.mul_apply,Matrix.one_apply,if_true] using hh
  have hlower:1≤‖A i i‖*C+δ*C:=by
    calc
      _=‖∑j,A i j*A⁻¹ j i‖:=by rw [he,norm_one]
      _≤∑j,‖A i j*A⁻¹ j i‖:=norm_sum_le _ _
      _≤∑j,((if j=i then ‖A i i‖*C else 0)+δ*‖A⁻¹ j i‖):=Finset.sum_le_sum (fun j _=>hp j)
      _=‖A i i‖*C+δ*(∑j,‖A⁻¹ j i‖):=by
        rw [Finset.sum_add_distrib,←Finset.mul_sum]
        simp
      _≤_:=add_le_add_left (mul_le_mul_of_nonneg_left (hcol i) hδ) _
  have hn:0<‖A i i‖:=by
    by_contra h
    have hz:‖A i i‖=0:=le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hz,zero_mul,zero_add] at hlower
    linarith
  refine ⟨norm_pos_iff.mp hn,?_⟩
  rw [norm_inv,inv_eq_one_div]
  apply (div_le_iff₀ hn).mpr
  nlinarith only [hlower,hsmall]

theorem principal_near_diagonal_inverse_rows_cols (A:Matrix I I ℂ)(hA:IsUnit A)(hsym:A.IsSymm)
    (E:Set I)(hE:IsUnit (A.submatrix (Subtype.val:E→I) (Subtype.val:E→I)))
    (C δ:ℝ)(hC:0≤C)(hδ:0≤δ)
    (hcol:∀i,∑j,‖A⁻¹ j i‖≤C)(hoff:∀i j,i≠j→‖A i j‖≤δ)
    (hsmall:δ*C≤1/2)(hsmallE:(Fintype.card E:ℝ)*(2*C)*δ≤1/2) :
    (∀i:E,∑j:E,‖(A.submatrix (Subtype.val:E→I) (Subtype.val:E→I))⁻¹ i j‖≤4*C) ∧
      (∀j:E,∑i:E,‖(A.submatrix (Subtype.val:E→I) (Subtype.val:E→I))⁻¹ i j‖≤4*C) := by
  let P:=A.submatrix (Subtype.val:E→I) (Subtype.val:E→I)
  have hp:=diagonal_pivots_of_inverse_columns A hA C δ hC hδ hcol hoff hsmall
  have hdiag:∀i:E,P i i≠0:=fun i=>(hp i.val).1
  have hpivot:∀i:E,‖(P i i)⁻¹‖≤2*C:=fun i=>(hp i.val).2
  have herror:∀i:E,∑j:E,‖(P-Matrix.diagonal (fun k:E=>P k k)) i j‖≤(Fintype.card E:ℝ)*δ:=by
    intro i
    calc
      _≤∑_j:E,δ:=by
        apply Finset.sum_le_sum
        intro j _
        by_cases hij:i=j
        · subst j
          simpa only [Matrix.sub_apply,Matrix.diagonal_apply_eq,sub_self,norm_zero] using hδ
        · have hv:i.val≠j.val:=fun h=>hij (Subtype.ext h)
          simpa only [Matrix.sub_apply,Matrix.diagonal_apply_ne _ hij,sub_zero,P,Matrix.submatrix_apply] using hoff i.val j.val hv
      _=_:=by simp
  have hrow:∀i:E,∑j:E,‖P⁻¹ i j‖≤4*C:=by
    have hh:=inverse_rows_of_small_offdiagonal P hE (2*C) ((Fintype.card E:ℝ)*δ)
      (by positivity) (by positivity) hdiag hpivot herror (by nlinarith only [hsmallE])
    simpa only [show 2*(2*C)=4*C by ring] using hh
  have hPs:P⁻¹.IsSymm:=by
    have he:P.IsSymm:=hsym.submatrix _
    change P⁻¹.transpose=P⁻¹
    rw [Matrix.transpose_nonsing_inv,he]
  refine ⟨hrow,fun j=>?_⟩
  change (∑i:E,‖P⁻¹ i j‖)≤_
  calc
    _=∑i:E,‖P⁻¹ j i‖:=Finset.sum_congr rfl (fun i _=>congrArg norm (hPs.apply j i))
    _≤_:=hrow j

end LocalLaw
