import LocalLaw.OneSidedDiagonalComparison

/-! One-sided diagonal comparison with an actual charged-column sum. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
variable {V:Type}[Fintype V][DecidableEq V]

theorem inverse_diagonal_change_weighted_one_sided (A B:Matrix V V ℂ)(hA:IsUnit A)(hB:IsUnit B)
    (e:V→ℂ)(hchange:B-A=Matrix.diagonal e)(x y:V)(F D:ℝ)(hF:0≤F)
    (hleft:∀v,e v≠0→‖A⁻¹ x v‖≤F)
    (hright:(∑v,‖e v‖*‖B⁻¹ v y‖)≤D):
    ‖A⁻¹ x y-B⁻¹ x y‖≤F*D:=by
  have hid:A⁻¹-B⁻¹=A⁻¹*(B-A)*B⁻¹:=by
    rw [Matrix.inv_sub_inv (show IsUnit A↔IsUnit B from ⟨fun _=>hB,fun _=>hA⟩)]
  rw [hchange] at hid
  have heq:(A⁻¹*Matrix.diagonal e*B⁻¹) x y=∑v,A⁻¹ x v*(e v*B⁻¹ v y):=by
    simp [Matrix.mul_apply,Matrix.diagonal_apply,Finset.sum_mul,mul_assoc]
  have hh:=congrArg (fun M:Matrix V V ℂ=>M x y) hid
  change A⁻¹ x y-B⁻¹ x y=(A⁻¹*Matrix.diagonal e*B⁻¹) x y at hh
  rw [hh,heq]
  calc
    _≤∑v,‖A⁻¹ x v*(e v*B⁻¹ v y)‖:=norm_sum_le _ _
    _≤∑v,F*(‖e v‖*‖B⁻¹ v y‖):=by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv:e v=0
      · simp only [hv,zero_mul,mul_zero,norm_zero]
        exact le_rfl
      · simp only [norm_mul]
        exact mul_le_mul_of_nonneg_right (hleft v hv) (by positivity)
    _=F*∑v,‖e v‖*‖B⁻¹ v y‖:=(Finset.mul_sum ..).symm
    _≤_:=mul_le_mul_of_nonneg_left hright hF

omit [DecidableEq V] in
theorem weighted_sum_le_subtype_sum (p:V→Prop)[DecidablePred p](e f:V→ℝ)(w:ℝ)
    (_he:∀v,0≤e v)(hf:∀v,0≤f v)(hzero:∀v,¬p v→e v=0)(hw:∀v,e v≤w):
    (∑v,e v*f v)≤w*∑v:{v//p v},f v.val:=by
  have heq:(∑v,e v*f v)=∑v:{v//p v},e v.val*f v.val:=by
    exact (Fintype.sum_subtype_add_sum_subtype p (fun v=>e v*f v)).symm.trans (by
      simp only [show (∑v:{v//¬p v},e v.val*f v.val)=0 from
        Finset.sum_eq_zero (fun v _=>by rw [hzero v.val v.property,zero_mul]),add_zero])
  rw [heq,Finset.mul_sum]
  exact Finset.sum_le_sum (fun v _=>mul_le_mul_of_nonneg_right (hw v.val) (hf v.val))

end LocalLaw
