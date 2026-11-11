import LocalLaw.AttachedLeafMatrixBlocks

/-! # Core-neighbor row sums from actual leaf row sums

Each leaf column of the inverse equation recovers its mate column. Summing
the literal lost-neighbor incidences therefore preserves a uniform bound,
including repeated mates and a target that is itself a leaf.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance leafMateRowsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V I:Type} [Fintype V] [Fintype I] {d:ℕ}

theorem attachLeaves_column_leaf_equation (g:DeficientGraph V d)(hd:3≤d)
    (mate:I→V)(hr:∀v,multiLeafMultiplicity mate v≤g.deficit v)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(x:V⊕I)(l:I) :
    let G:=(g.attachLeaves (by omega) mate hr).extensionGreen q z
    G x (.inl (mate l))*treeEdgeWeight d+G x (.inr l)*(-z-q)=
      if x=.inr l then 1 else 0 := by
  dsimp only
  let H:=g.attachLeaves (by omega) mate hr
  let G:=H.extensionGreen q z
  let M:=H.extensionMatrix q z
  have hM:IsUnit M:=H.extensionMatrix_isUnit hd q z hz hq
  have hh:=congrArg (fun A:Matrix (V⊕I) (V⊕I) ℂ=>A x (.inr l))
    (Matrix.nonsing_inv_mul M ((Matrix.isUnit_iff_isUnit_det M).mp hM))
  dsimp only at hh
  simp only [Matrix.mul_apply,Fintype.sum_sum_type,Matrix.one_apply] at hh
  change (∑v:V,G x (.inl v)*M (.inl v) (.inr l))+
    (∑k:I,G x (.inr k)*M (.inr k) (.inr l))=_ at hh
  have hc (v:V):M (.inl v) (.inr l)=if v=mate l then treeEdgeWeight d else 0:=
    g.attachLeaves_extensionMatrix_core_leaf hd mate hr q z v l
  have hl (k:I):M (.inr k) (.inr l)=if k=l then -z-q else 0:=
    g.attachLeaves_extensionMatrix_leaf hd mate hr q z k l
  simp_rw [hc,hl] at hh
  simpa only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true] using hh

theorem attachLeaves_mate_row_bound (g:DeficientGraph V d)(hd:3≤d)
    (mate:I→V)(hr:∀v,multiLeafMultiplicity mate v≤g.deficit v)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(B W:ℝ)(hzB:‖z‖≤B)(hqnorm:‖q‖≤2)
    (hW:0≤W)(x:V⊕I)
    (hrow:(∑l:I,‖(g.attachLeaves (by omega) mate hr).extensionGreen q z x (.inr l)‖)≤W) :
    (∑l:I,‖(g.attachLeaves (by omega) mate hr).extensionGreen q z x (.inl (mate l))‖)≤
      ‖(treeEdgeWeight d)⁻¹‖*(1+(B+2)*W) := by
  let G:=(g.attachLeaves (by omega) mate hr).extensionGreen q z
  let α:=treeEdgeWeight d
  have hα:α≠0:=by
    have he:=treeEdgeWeight_norm_sq d hd
    have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
    have hp:0<‖α‖^2:=by
      dsimp only [α]
      rw [he]
      exact one_div_pos.mpr (by linarith)
    intro hzα
    simp only [hzα,norm_zero,zero_pow (by decide:2≠0)] at hp
    linarith
  have hB:0≤B:=(norm_nonneg z).trans hzB
  have hscalar:‖z+q‖≤B+2:=(norm_add_le z q).trans (add_le_add hzB hqnorm)
  have he (l:I):G x (.inl (mate l))=
      ((if x=.inr l then 1 else 0)+G x (.inr l)*(z+q))*α⁻¹:=by
    have hh:=g.attachLeaves_column_leaf_equation hd mate hr q z hz hq x l
    change G x (.inl (mate l))*α+G x (.inr l)*(-z-q)=_ at hh
    change G x (.inl (mate l))=((if x=.inr l then 1 else 0)+G x (.inr l)*(z+q))/α
    apply (eq_div_iff hα).mpr
    linear_combination hh
  have hp (l:I):‖G x (.inl (mate l))‖≤
      ‖α⁻¹‖*((if x=.inr l then 1 else 0)+(B+2)*‖G x (.inr l)‖):=by
    rw [he l,norm_mul]
    have hi:‖(if x=.inr l then (1:ℂ) else 0)‖=(if x=.inr l then (1:ℝ) else 0):=by
      split_ifs <;> simp
    have hn:‖(if x=.inr l then (1:ℂ) else 0)+G x (.inr l)*(z+q)‖≤
        (if x=.inr l then (1:ℝ) else 0)+(B+2)*‖G x (.inr l)‖:=by
      exact (norm_add_le _ _).trans ((add_le_add_left
        ((by simpa only [norm_mul,mul_comm] using
          mul_le_mul_of_nonneg_left hscalar (norm_nonneg (G x (.inr l))))) _).trans_eq (by rw [hi]))
    exact (mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hdelta:(∑l:I,if x=.inr l then (1:ℝ) else 0)≤1:=by
    rcases x with v|k
    · simp
    · simp [eq_comm]
  calc
    _≤∑l:I,‖α⁻¹‖*((if x=.inr l then 1 else 0)+(B+2)*‖G x (.inr l)‖):=
      Finset.sum_le_sum (fun l _=>hp l)
    _=‖α⁻¹‖*((∑l:I,if x=.inr l then (1:ℝ) else 0)+(B+2)*(∑l:I,‖G x (.inr l)‖)):=by
      rw [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.mul_sum]
    _≤‖α⁻¹‖*(1+(B+2)*W):=mul_le_mul_of_nonneg_left
      (add_le_add hdelta (mul_le_mul_of_nonneg_left hrow (by linarith))) (norm_nonneg _)
    _=_:=rfl

end DeficientGraph
end LocalLaw
