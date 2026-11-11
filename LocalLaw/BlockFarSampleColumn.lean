import LocalLaw.BlockSchur

/-! # Far sampled columns from a common-core row and a nearly diagonal block

The diagonal sampled term retains its far-core factor. All off-diagonal
terms pay the true core-to-sample L1 sum, without a sample-count loss.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance blockFarSampleDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem finite_near_diagonal_column_bound {I:Type} [Fintype I] [DecidableEq I]
    (c:I→ℂ)(R:Matrix I I ℂ)(b:I)(K δ f a:ℝ)
    (hK:0≤K)(hδ:0≤δ)(hf:0≤f)
    (hdiag:‖R b b‖≤K)(hoff:∀i,i≠b→‖R i b‖≤δ)
    (hc:‖c b‖≤f)(hL1:(∑i,‖c i‖)≤a) :
    ‖∑i,c i*R i b‖≤K*f+δ*a := by
  have hp (i:I):‖c i*R i b‖≤(if i=b then K*f else 0)+δ*‖c i‖:=by
    rw [norm_mul]
    by_cases hi:i=b
    · subst i
      simp only [if_true]
      have hh:=mul_le_mul hc hdiag (norm_nonneg _) hf
      nlinarith [mul_nonneg hδ (norm_nonneg (c b))]
    · simp only [if_neg hi,zero_add]
      exact (mul_le_mul_of_nonneg_left (hoff i hi) (norm_nonneg _)).trans_eq (mul_comm _ _)
  calc
    _≤∑i,‖c i*R i b‖:=norm_sum_le _ _
    _≤∑i,((if i=b then K*f else 0)+δ*‖c i‖):=Finset.sum_le_sum (fun i _=>hp i)
    _=K*f+δ*(∑i,‖c i‖):=by
      rw [Finset.sum_add_distrib,←Finset.mul_sum]
      simp
    _≤_:=add_le_add_left (mul_le_mul_of_nonneg_left hL1 hδ) _

section Block
variable {I J:Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem inverse_block12_from_core (M:Matrix (I⊕J) (I⊕J) ℂ)
    (hM:IsUnit M)(hc:IsUnit M.toBlocks₁₁) :
    (M⁻¹).toBlocks₁₂= -(M.toBlocks₁₁⁻¹*M.toBlocks₁₂*(M⁻¹).toBlocks₂₂) := by
  have hmul:M*M⁻¹=1:=Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hM)
  have he:M.toBlocks₁₁*(M⁻¹).toBlocks₁₂+M.toBlocks₁₂*(M⁻¹).toBlocks₂₂=0:=by
    ext i j
    have hh:=congrArg (fun A:Matrix (I⊕J) (I⊕J) ℂ=>A (.inl i) (.inr j)) hmul
    simpa only [Matrix.mul_apply,Fintype.sum_sum_type,Matrix.add_apply,
      Matrix.toBlocks₁₁,Matrix.toBlocks₁₂,Matrix.toBlocks₂₂,Matrix.of_apply,
      Matrix.one_apply,Sum.inl_ne_inr,if_false,Matrix.zero_apply] using hh
  have hh:=congrArg (fun A:Matrix I J ℂ=>M.toBlocks₁₁⁻¹*A) he
  dsimp only at hh
  rw [Matrix.mul_add,←Matrix.mul_assoc,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hc),
    Matrix.one_mul,Matrix.mul_zero] at hh
  rw [←Matrix.mul_assoc] at hh
  exact eq_neg_iff_add_eq_zero.mpr hh

theorem inverse_block12_far_column (M:Matrix (I⊕J) (I⊕J) ℂ)
    (hM:IsUnit M)(hc:IsUnit M.toBlocks₁₁)(x:I)(b:J)(K δ f a:ℝ)
    (hK:0≤K)(hδ:0≤δ)(hf:0≤f)
    (hdiag:‖(M⁻¹).toBlocks₂₂ b b‖≤K)
    (hoff:∀j,j≠b→‖(M⁻¹).toBlocks₂₂ j b‖≤δ)
    (hfar:‖(M.toBlocks₁₁⁻¹*M.toBlocks₁₂) x b‖≤f)
    (hL1:(∑j,‖(M.toBlocks₁₁⁻¹*M.toBlocks₁₂) x j‖)≤a) :
    ‖M⁻¹ (.inl x) (.inr b)‖≤K*f+δ*a := by
  have hh:=congrArg (fun A:Matrix I J ℂ=>A x b) (inverse_block12_from_core M hM hc)
  change M⁻¹ (.inl x) (.inr b)= -_ at hh
  rw [hh,norm_neg,Matrix.mul_apply]
  exact finite_near_diagonal_column_bound _ _ b K δ f a hK hδ hf hdiag hoff hfar hL1

end Block
end LocalLaw
