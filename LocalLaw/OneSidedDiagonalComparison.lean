import LocalLaw.MinorIdentity

/-! One-sided decay is sufficient for a genuine diagonal model change. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
variable {V:Type}[Fintype V][DecidableEq V]

theorem inverse_diagonal_change_one_sided (A B:Matrix V V ℂ)(hA:IsUnit A)(hB:IsUnit B)
    (e:V→ℂ)(hchange:B-A=Matrix.diagonal e)(x y:V)(f C:ℝ)(hf:0≤f)(_hC:0≤C)
    (hleft:∀v,e v≠0→‖A⁻¹ x v‖≤f)(hright:∀v,e v≠0→‖B⁻¹ v y‖≤C):
    ‖A⁻¹ x y-B⁻¹ x y‖≤f*C*(∑v,‖e v‖):=by
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
    _≤∑v,f*(‖e v‖*C):=by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv:e v=0
      · simp only [hv,zero_mul,mul_zero,norm_zero]
        exact le_rfl
      · simp only [norm_mul]
        exact mul_le_mul (hleft v hv)
          (mul_le_mul_of_nonneg_left (hright v hv) (norm_nonneg _))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hf
    _=f*C*(∑v,‖e v‖):=by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro v _;ring

end LocalLaw
