import LocalLaw.BoundaryChargeGram
import LocalLaw.BlockSchur

/-! # Missing-degree Gram identity for arbitrary deficient models

The inherited deficit cancels from the difference between a full model's
boundary diagonal and the boundary diagonal of its vertex restriction.
Only the actual crossing edges remain, with their complete multiplicities.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance deficientBoundaryGramDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type*}[Fintype V][DecidableEq V]

omit [DecidableEq V] in
theorem graph_boundary_inner_fiber_degree_loss (G:SimpleGraph V)(T:Set V)(x:T) :
    Nat.card {a:BoundaryOrientedEdge G T //x.val=a.val.1}=
      G.degree x.val-(G.induce T).degree x := by
  have hh:=Nat.card_congr (innerNeighborPartitionEquiv G T x)
  rw [Nat.card_sum] at hh
  simp only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] at hh
  rw [Nat.card_congr (boundaryInnerNeighborEquiv G T x)]
  simp only [Nat.card_eq_fintype_card]
  omega

namespace DeficientGraph
variable {d:ℕ}

theorem restrict_boundaryDiagonal_difference_eq_cutGram (g:DeficientGraph V d)(hd:3≤d)(T:Set V) :
    (g.restrict T).boundaryDiagonal-
      g.boundaryDiagonal.submatrix (Subtype.val:T→V) (Subtype.val:T→V)=
      cutInnerCoupling g.graph d T*(cutInnerCoupling g.graph d T).transpose := by
  let c:ℂ:=↑((Real.sqrt ((d:ℝ)-1))⁻¹)
  have hD:(3:ℝ)≤d:=Nat.cast_le.mpr hd
  have hc:c^2=(↑(((d:ℝ)-1)⁻¹):ℂ) := by
    dsimp only [c]
    rw [←Complex.ofReal_pow,inv_pow,Real.sq_sqrt (by linarith : (0:ℝ)≤d-1)]
  ext x y
  by_cases hxy:x=y
  · subst y
    have hdeg:(g.graph.induce T).degree x≤g.graph.degree x.val := induced_degree_le g.graph T x
    have hsum:(∑a:BoundaryOrientedEdge g.graph T,if x.val=a.val.1 then c^2 else 0)=
        (↑(g.graph.degree x.val-(g.graph.induce T).degree x):ℂ)*c^2 := by
      rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
      congr 1
      have hh:=graph_boundary_inner_fiber_degree_loss g.graph T x
      simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using congrArg (fun n:ℕ=>(n:ℂ)) hh
    have hentry:(cutInnerCoupling g.graph d T*(cutInnerCoupling g.graph d T).transpose) x x=
        ∑a:BoundaryOrientedEdge g.graph T,if x.val=a.val.1 then c^2 else 0 := by
      simp only [Matrix.mul_apply,Matrix.transpose_apply,cutInnerCoupling]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp only [mul_zero,sq]
      rfl
    rw [hentry,hsum,hc]
    simp only [boundaryDiagonal,Matrix.sub_apply,Matrix.submatrix_apply,Matrix.diagonal_apply_eq,
      boundaryCoefficient,restrict,Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_natCast,
      Complex.ofReal_one,Nat.cast_sub hdeg]
    push_cast
    field_simp [show ((d:ℂ)-1)≠0 by exact_mod_cast (by linarith : (d:ℝ)-1≠0)]
  · have hval:x.val≠y.val:=fun h=>hxy (Subtype.ext h)
    simp only [boundaryDiagonal,Matrix.sub_apply,Matrix.submatrix_apply,Matrix.diagonal_apply,
      if_neg hxy,if_neg hval,sub_self]
    symm
    apply Finset.sum_eq_zero
    intro a _
    change (if x.val=a.val.1 then c else 0)*(if y.val=a.val.1 then c else 0)=0
    by_cases hx:x.val=a.val.1
    · have hy:y.val≠a.val.1:=fun hy=>hval (hx.trans hy.symm)
      simp only [hx,hy,if_true,if_false,mul_zero]
    · simp only [hx,if_false,zero_mul]

theorem extensionMatrix_retained_block (g:DeficientGraph V d)(hd:3≤d)(T:Set V)(q z:ℂ) :
    (g.extensionMatrix q z).submatrix (Subtype.val:T→V) (Subtype.val:T→V)=
      (g.restrict T).extensionMatrix q z+
        q•(cutInnerCoupling g.graph d T*(cutInnerCoupling g.graph d T).transpose) := by
  have hGram:=g.restrict_boundaryDiagonal_difference_eq_cutGram hd T
  have hs:=spectralMatrix_principal g.H z (Subtype.val:T→V) Subtype.val_injective
  rw [←g.H_restrict T] at hs
  ext i j
  have hD:=congrFun (congrFun hGram i) j
  have hS:=congrFun (congrFun hs i) j
  simp only [Matrix.sub_apply,Matrix.submatrix_apply] at hD
  simp only [Matrix.submatrix_apply] at hS
  simp only [extensionMatrix,boundaryMatrix,Matrix.submatrix_apply,Matrix.sub_apply,
    Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  rw [←hS]
  linear_combination q*hD

end DeficientGraph
end LocalLaw
