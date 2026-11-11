import LocalLaw.WeightedWoodburyTarget

/-! # Exact inverse comparison when the sampled blocks are restored

Two core Green matrices may differ while the restored sampled couplings
and sampled precision agree. The full inverse difference factors through
the core Green difference, with actual full-kernel harmonic weights. This
identity includes targets that lie in the restored sampled block.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance coreSchurLiftDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {I J:Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem core_schur_inverse_difference (M N:Matrix (I⊕J) (I⊕J) ℂ)
    (hM:IsUnit M)(hN:IsUnit N)(R P:Matrix I I ℂ)(hR:IsUnit R)(hP:IsUnit P)
    (hM11:M.toBlocks₁₁=R⁻¹)(hN11:N.toBlocks₁₁=P⁻¹)
    (h12:M.toBlocks₁₂=N.toBlocks₁₂)(h21:M.toBlocks₂₁=N.toBlocks₂₁)
    (h22:M.toBlocks₂₂=N.toBlocks₂₂) :
    M⁻¹-N⁻¹=(M⁻¹.submatrix id Sum.inl*R⁻¹)*(R-P)*(P⁻¹*N⁻¹.submatrix Sum.inl id) := by
  let e:I↪I⊕J:=⟨Sum.inl,Sum.inl_injective⟩
  have hs:∀x y,x∉Set.range e∨y∉Set.range e→(N-M) x y=0:=by
    intro x y hxy
    rcases x with i|j <;> rcases y with i'|j'
    · exact False.elim (hxy.elim (fun h=>h ⟨i,rfl⟩) (fun h=>h ⟨i',rfl⟩))
    · have he:=congrArg (fun A:Matrix I J ℂ=>A i j') h12
      exact sub_eq_zero.mpr he.symm
    · have he:=congrArg (fun A:Matrix J I ℂ=>A j i') h21
      exact sub_eq_zero.mpr he.symm
    · have he:=congrArg (fun A:Matrix J J ℂ=>A j j') h22
      exact sub_eq_zero.mpr he.symm
  have hd:(N-M).submatrix e e=P⁻¹-R⁻¹:=by
    change N.toBlocks₁₁-M.toBlocks₁₁=P⁻¹-R⁻¹
    rw [hM11,hN11]
  have hRi:R⁻¹*R=1:=Matrix.nonsing_inv_mul R ((Matrix.isUnit_iff_isUnit_det R).mp hR)
  have hPi:P*P⁻¹=1:=Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP)
  have hcore:P⁻¹-R⁻¹=R⁻¹*(R-P)*P⁻¹:=by
    rw [Matrix.mul_sub,Matrix.sub_mul,hRi,Matrix.one_mul,Matrix.mul_assoc,hPi,Matrix.mul_one]
  have hh:M⁻¹-N⁻¹=M⁻¹*(N-M)*N⁻¹:=by
    rw [Matrix.inv_sub_inv (show IsUnit M↔IsUnit N from ⟨fun _=>hN,fun _=>hM⟩)]
  rw [hh,supported_single_middle_product e M⁻¹ (N-M) N⁻¹ hs,hd,hcore]
  simp only [Matrix.mul_assoc]
  rfl

theorem left_core_lift_entry (M:Matrix (I⊕J) (I⊕J) ℂ)(hM:IsUnit M)
    (R:Matrix I I ℂ)(h11:M.toBlocks₁₁=R⁻¹)(x:I⊕J)(u:I) :
    (M⁻¹.submatrix id Sum.inl*R⁻¹) x u=
      (if x=.inl u then 1 else 0)-∑b:J,M⁻¹ x (.inr b)*M (.inr b) (.inl u) := by
  have hh:=congrArg (fun A:Matrix (I⊕J) (I⊕J) ℂ=>A x (.inl u))
    (Matrix.nonsing_inv_mul M ((Matrix.isUnit_iff_isUnit_det M).mp hM))
  dsimp only at hh
  simp only [Matrix.mul_apply,Fintype.sum_sum_type,Matrix.one_apply] at hh
  have hc (i:I):M (.inl i) (.inl u)=R⁻¹ i u:=congrArg (fun A:Matrix I I ℂ=>A i u) h11
  simp_rw [hc] at hh
  change (∑i:I,M⁻¹ x (.inl i)*R⁻¹ i u)=_
  linear_combination hh

theorem right_core_lift_entry (M:Matrix (I⊕J) (I⊕J) ℂ)(hM:IsUnit M)
    (R:Matrix I I ℂ)(h11:M.toBlocks₁₁=R⁻¹)(u:I)(y:I⊕J) :
    (R⁻¹*M⁻¹.submatrix Sum.inl id) u y=
      (if (.inl u:I⊕J)=y then 1 else 0)-∑b:J,M (.inl u) (.inr b)*M⁻¹ (.inr b) y := by
  have hh:=congrArg (fun A:Matrix (I⊕J) (I⊕J) ℂ=>A (.inl u) y)
    (Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hM))
  dsimp only at hh
  simp only [Matrix.mul_apply,Fintype.sum_sum_type,Matrix.one_apply] at hh
  have hc (i:I):M (.inl u) (.inl i)=R⁻¹ u i:=congrArg (fun A:Matrix I I ℂ=>A u i) h11
  simp_rw [hc] at hh
  change (∑i:I,R⁻¹ u i*M⁻¹ (.inl i) y)=_
  linear_combination hh

end LocalLaw
