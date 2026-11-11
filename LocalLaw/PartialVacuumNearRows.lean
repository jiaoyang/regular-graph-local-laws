import LocalLaw.PartialTripleRows

/-! # Partial vacuum rows with a free scalar cap

The approximate cavity parameter may lie just outside the unit disk. These
estimates use a common bound for q and its formal reference p, while only
the normalized edge factor alpha*q is required to have norm at most one.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialVacuumNearRowsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {L:Type} [Fintype L] [DecidableEq L]

theorem partialVacuum_inverse_rows_cap (A B:Set L) (A₀:Matrix A A ℂ) (m p α:ℂ)
    (hm:m≠0) (hp:p≠0) (P:ℝ) (hP:0≤P) (hmnorm:‖m‖≤P) (hpnorm:‖p‖≤P) (ha:‖α*m‖≤1)
    (K:ℝ) (hK:0≤K)
    (hrestored:IsUnit (A₀-Matrix.diagonal (fun _:A=>m*α^2)))
    (hrows:∀ a,∑ a',‖(A₀-Matrix.diagonal (fun _:A=>m*α^2))⁻¹ a a'‖≤K) :
    let E:=partialMatchingCoupling A B α
    let M:=Matrix.fromBlocks (A₀-partialMissingCharge A B m α) E E.transpose (partialVacuumDiagonal A B m p)
    ∀ u,∑ v,‖M⁻¹ u v‖≤P+2*K := by
  dsimp only
  let E:=partialMatchingCoupling A B α
  let D:=partialVacuumDiagonal A B m p
  let M:=Matrix.fromBlocks (A₀-partialMissingCharge A B m α) E E.transpose D
  have hv:=partialVacuum_schur A B A₀ m p α hm hp hrestored
  have hM:IsUnit M:=hv.1
  obtain ⟨hD,hDinv⟩:=partialVacuumDiagonal_inverse A B m p hm hp
  have hS:∀ a,∑ a',‖(blockSchur M)⁻¹ a a'‖≤K:=by
    rw [←inverse_block11 M hM hD,hv.2]
    exact hrows
  have hDrows:∀ b,∑ b',‖D⁻¹ b b'‖≤P:=by
    intro b
    rw [hDinv]
    have hh:(∑ b',‖partialVacuumInverse A B m p b b'‖)=‖if b.val∈A then m else p‖:=by
      simp [partialVacuumInverse,Matrix.diagonal_apply,apply_ite norm]
    rw [hh]
    split_ifs
    · exact hmnorm
    · exact hpnorm
  have products:=partialMatching_vacuum_products A B m p α
  have hLeft:∀ a,∑ b,‖(M.toBlocks₁₂*M.toBlocks₂₂⁻¹) a b‖≤‖α*m‖:=by
    change ∀ a,∑ b,‖(E*D⁻¹) a b‖≤‖α*m‖
    rw [hDinv,products.1]
    exact partialMatching_row_sum A B (α*m)
  have hRight:∀ b,∑ a,‖(M.toBlocks₂₂⁻¹*M.toBlocks₂₁) b a‖≤‖α*m‖:=by
    change ∀ b,∑ a,‖(D⁻¹*E.transpose) b a‖≤‖α*m‖
    rw [hDinv,products.2]
    exact partialMatching_row_sum B A (α*m)
  exact block_inverse_row_sum_bound M hM hD K P ‖α*m‖ hK hP (norm_nonneg _) ha hS hDrows hLeft hRight

theorem partialTripleNewPrecision_inverse_rows_cap (A B C:Set L) (A₀:Matrix A A ℂ) (m p α:ℂ)
    (hm:m≠0) (hp:p≠0) (P:ℝ) (hP:0≤P) (hmnorm:‖m‖≤P) (hpnorm:‖p‖≤P) (ha:‖α*m‖≤1)
    (K:ℝ) (hK:0≤K)
    (hrestored:IsUnit (A₀-Matrix.diagonal (fun _:A=>m*α^2)))
    (hrows:∀ a,∑ a',‖(A₀-Matrix.diagonal (fun _:A=>m*α^2))⁻¹ a a'‖≤K) :
    IsUnit (partialTripleNewPrecision A B C A₀ m p α)∧
      ∀ u,∑ v,‖(partialTripleNewPrecision A B C A₀ m p α)⁻¹ u v‖≤P+2*K := by
  let M:=Matrix.fromBlocks (A₀-partialMissingCharge A B m α)
    (partialMatchingCoupling A B α) (partialMatchingCoupling A B α).transpose
    (partialVacuumDiagonal A B m p)
  have hM:IsUnit M:=(partialVacuum_schur A B A₀ m p α hm hp hrestored).1
  let D:Matrix C C ℂ:=Matrix.diagonal (fun _=>m⁻¹)
  have hDprod:D*Matrix.diagonal (fun _:C=>m)=1:=by
    ext c c'
    by_cases hc:c=c' <;> simp [D,Matrix.diagonal_apply,Matrix.mul_apply,Matrix.one_apply,hc,hm]
  have hD:IsUnit D:=Matrix.isUnit_of_right_inverse hDprod
  have hDinv:D⁻¹=Matrix.diagonal (fun _:C=>m):=Matrix.inv_eq_right_inv hDprod
  have hfull:=blockDiagonal_inverse M D hM hD
  let e:=(Equiv.sumAssoc A B C).symm
  have hnew:partialTripleNewPrecision A B C A₀ m p α=(Matrix.fromBlocks M 0 0 D).submatrix e e:=rfl
  constructor
  · rw [hnew]
    exact (Matrix.isUnit_submatrix_equiv e e).mpr hfull.1
  · intro u
    rw [hnew,Matrix.inv_submatrix_equiv,hfull.2]
    have heq:(∑ v,‖(Matrix.fromBlocks M⁻¹ 0 0 D⁻¹).submatrix e e u v‖)=
        ∑ v,‖Matrix.fromBlocks M⁻¹ 0 0 D⁻¹ (e u) v‖:=
      e.sum_comp (fun v=>‖Matrix.fromBlocks M⁻¹ 0 0 D⁻¹ (e u) v‖)
    rw [heq]
    rcases e u with a | c
    · simpa only [Fintype.sum_sum_type,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply,norm_zero,Finset.sum_const_zero,add_zero] using
        partialVacuum_inverse_rows_cap A B A₀ m p α hm hp P hP hmnorm hpnorm ha K hK hrestored hrows a
    · rw [Fintype.sum_sum_type,hDinv]
      simp only [Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,
        norm_zero,Finset.sum_const_zero,zero_add]
      have hh:(∑ v:C,‖Matrix.diagonal (fun _:C=>m) c v‖)=‖m‖:=by
        simp [Matrix.diagonal_apply,apply_ite norm]
      rw [hh]
      linarith

theorem partialTripleNewPrecision_inverse_columns_cap (A B C:Set L) (A₀:Matrix A A ℂ) (m p α:ℂ)
    (hA:A₀.IsSymm) (hm:m≠0) (hp:p≠0) (P:ℝ) (hP:0≤P) (hmnorm:‖m‖≤P) (hpnorm:‖p‖≤P) (ha:‖α*m‖≤1)
    (K:ℝ) (hK:0≤K)
    (hrestored:IsUnit (A₀-Matrix.diagonal (fun _:A=>m*α^2)))
    (hrows:∀ a,∑ a',‖(A₀-Matrix.diagonal (fun _:A=>m*α^2))⁻¹ a a'‖≤K) :
    ∀ v,∑ u,‖(partialTripleNewPrecision A B C A₀ m p α)⁻¹ u v‖≤P+2*K := by
  have hs:((partialTripleNewPrecision A B C A₀ m p α)⁻¹).IsSymm:=by
    change ((partialTripleNewPrecision A B C A₀ m p α)⁻¹).transpose=_
    rw [Matrix.transpose_nonsing_inv,(partialTripleNewPrecision_isSymm A B C A₀ m p α hA).eq]
  intro v
  have heq:(∑ u,‖(partialTripleNewPrecision A B C A₀ m p α)⁻¹ u v‖)=
      ∑ u,‖(partialTripleNewPrecision A B C A₀ m p α)⁻¹ v u‖:=
    Finset.sum_congr rfl (fun u _=>congrArg norm (hs.apply v u))
  rw [heq]
  exact (partialTripleNewPrecision_inverse_rows_cap A B C A₀ m p α hm hp P hP hmnorm hpnorm ha K hK hrestored hrows).2 v

end LocalLaw
