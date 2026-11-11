import LocalLaw.VacuumLeafSchur

/-! # Uniform full vacuum rows with repeated core mates -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance vacuumLeafRowsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {K J:Type} [Fintype K] [Fintype J] [DecidableEq K] [DecidableEq J]

theorem vacuumLeaf_inverse_rows (mate:J→Option K) (A:Matrix K K ℂ) (degree:K→ℂ) (q p α:ℂ)
    (hq:q≠0) (hp:p≠0) (P C a:ℝ) (hP:0≤P) (hC:0≤C) (ha:0≤a)
    (hqnorm:‖q‖≤P) (hpnorm:‖p‖≤P) (hαq:‖α*q‖≤1)
    (hmultiplicity:∀k,(Nat.card {j:J//mate j=some k}:ℝ)≤a)
    (hcore:IsUnit (A-Matrix.diagonal (fun k=>q*α^2*degree k)))
    (hrows:∀k,∑k',‖(A-Matrix.diagonal (fun k=>q*α^2*degree k))⁻¹ k k'‖≤C) :
    ∀u,∑v,‖(vacuumLeafMatrix mate A degree q p α)⁻¹ u v‖≤P+(1+a)*C := by
  let M:=vacuumLeafMatrix mate A degree q p α
  have hSchur:=vacuumLeaf_schur mate A degree q p α hq hp hcore
  obtain ⟨hD,hDinv⟩:=vacuumLeafDiagonal_inverse mate q p hq hp
  have hS:∀k,∑k',‖(blockSchur M)⁻¹ k k'‖≤C:=by
    rw [hSchur.2.1]
    exact hrows
  have hDrows:∀j,∑j',‖(vacuumLeafDiagonal mate q p)⁻¹ j j'‖≤P:=by
    intro j
    rw [hDinv]
    have hh:(∑j',‖vacuumLeafInverse mate q p j j'‖)=‖if mate j=none then p else q‖:=by
      simp [vacuumLeafInverse,Matrix.diagonal_apply,apply_ite norm]
    rw [hh]
    split_ifs
    · exact hpnorm
    · exact hqnorm
  have hproducts:=vacuumLeaf_products mate q p α
  have hLeft:∀k,∑j,‖(M.toBlocks₁₂*M.toBlocks₂₂⁻¹) k j‖≤a:=by
    change ∀k,∑j,‖(vacuumLeafIncidence mate α*(vacuumLeafDiagonal mate q p)⁻¹) k j‖≤a
    rw [hDinv,hproducts.1]
    intro k
    rw [vacuumLeafIncidence_row]
    exact (mul_le_mul_of_nonneg_left hαq (Nat.cast_nonneg _)).trans
      (by simpa only [mul_one] using hmultiplicity k)
  have hRight:∀j,∑k,‖(M.toBlocks₂₂⁻¹*M.toBlocks₂₁) j k‖≤1:=by
    change ∀j,∑k,‖((vacuumLeafDiagonal mate q p)⁻¹*(vacuumLeafIncidence mate α).transpose) j k‖≤1
    rw [hDinv,hproducts.2]
    intro j
    exact (vacuumLeafIncidence_column mate (α*q) j).trans hαq
  exact block_inverse_row_sum_bound_asymmetric M hSchur.1 hD C P a hC hP ha hS hDrows hLeft hRight

theorem vacuumLeaf_inverse_columns (mate:J→Option K) (A:Matrix K K ℂ) (degree:K→ℂ) (q p α:ℂ)
    (hA:A.IsSymm) (hq:q≠0) (hp:p≠0) (P C a:ℝ) (hP:0≤P) (hC:0≤C) (ha:0≤a)
    (hqnorm:‖q‖≤P) (hpnorm:‖p‖≤P) (hαq:‖α*q‖≤1)
    (hmultiplicity:∀k,(Nat.card {j:J//mate j=some k}:ℝ)≤a)
    (hcore:IsUnit (A-Matrix.diagonal (fun k=>q*α^2*degree k)))
    (hrows:∀k,∑k',‖(A-Matrix.diagonal (fun k=>q*α^2*degree k))⁻¹ k k'‖≤C) :
    ∀v,∑u,‖(vacuumLeafMatrix mate A degree q p α)⁻¹ u v‖≤P+(1+a)*C := by
  let M:=vacuumLeafMatrix mate A degree q p α
  have hs:M.transpose=M:=by
    change A.transpose=A at hA
    simp only [M,vacuumLeafMatrix,Matrix.fromBlocks_transpose,Matrix.transpose_sub,
      Matrix.diagonal_transpose,Matrix.transpose_transpose,vacuumLeafDiagonal,hA]
  have hInv:(M⁻¹).IsSymm:=by
    change (M⁻¹).transpose=M⁻¹
    rw [Matrix.transpose_nonsing_inv,hs]
  intro v
  have heq:(∑u,‖M⁻¹ u v‖)=∑u,‖M⁻¹ v u‖:=
    Finset.sum_congr rfl (fun u _=>congrArg norm (hInv.apply v u))
  rw [heq]
  exact vacuumLeaf_inverse_rows mate A degree q p α hq hp P C a hP hC ha hqnorm hpnorm hαq hmultiplicity hcore hrows v

end LocalLaw
