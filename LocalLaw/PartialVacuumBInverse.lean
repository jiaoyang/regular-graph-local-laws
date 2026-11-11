import LocalLaw.PartialVacuumNearRows
import LocalLaw.DeletionStability

/-! # Genuine inverse rows of the sampled-B Green block

Eliminate the old A block with precisely the missing-mate deficits restored.
The resulting Schur precision bounds the inverse B Green block. No lower
bound for individual B pivots and no switched-graph reference class occurs.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialVacuumBInverseDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {L:Type} [Fintype L] [DecidableEq L]

theorem partialVacuum_BGreen_inverse_rows (A B:Set L)(A₀:Matrix A A ℂ)(q p α:ℂ)
    (hq:q≠0)(hp:p≠0)(P K:ℝ)(hP:0≤P)(hK:0≤K)
    (hqinv:‖q⁻¹‖≤P)(hpinv:‖p⁻¹‖≤P)
    (hrestored:IsUnit (A₀-Matrix.diagonal (fun _:A=>q*α^2)))
    (hmissing:IsUnit (A₀-partialMissingCharge A B q α))
    (hrows:∀a,∑a',‖(A₀-partialMissingCharge A B q α)⁻¹ a a'‖≤K) :
    let E:=partialMatchingCoupling A B α
    let M:=Matrix.fromBlocks (A₀-partialMissingCharge A B q α) E E.transpose (partialVacuumDiagonal A B q p)
    IsUnit (M⁻¹).toBlocks₂₂ ∧
      (∀b,∑b',‖(M⁻¹).toBlocks₂₂⁻¹ b b'‖≤P+‖α‖^2*K) := by
  dsimp only
  let E:=partialMatchingCoupling A B α
  let M:=Matrix.fromBlocks (A₀-partialMissingCharge A B q α) E E.transpose (partialVacuumDiagonal A B q p)
  have hM:IsUnit M:=(partialVacuum_schur A B A₀ q p α hq hp hrestored).1
  have hc:IsUnit M.toBlocks₁₁:=hmissing
  have hh:=inverse_block22 M hM hc
  have hu:IsUnit (M⁻¹).toBlocks₂₂:=by
    rw [hh.2]
    exact Matrix.isUnit_nonsing_inv_iff.mpr hh.1
  have hi:(M⁻¹).toBlocks₂₂⁻¹=M.toBlocks₂₂-M.toBlocks₂₁*M.toBlocks₁₁⁻¹*M.toBlocks₁₂:=by
    rw [hh.2]
    exact Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hh.1)
  have hE:∀a,∑b,‖E a b‖≤‖α‖:=partialMatching_row_sum A B α
  have hEt:∀b,∑a,‖E.transpose b a‖≤‖α‖:=by
    intro b
    have he:E.transpose=partialMatchingCoupling B A α:=by
      ext b a
      simp only [E,partialMatchingCoupling,Matrix.transpose_apply,eq_comm]
    rw [he]
    exact partialMatching_row_sum B A α b
  have hprod:∀b,∑b',‖(M.toBlocks₂₁*M.toBlocks₁₁⁻¹*M.toBlocks₁₂) b b'‖≤‖α‖^2*K:=by
    have hf:=rectangular_product_row_sum_bound E.transpose (A₀-partialMissingCharge A B q α)⁻¹
      ‖α‖ K hK hEt hrows
    have hg:=rectangular_product_row_sum_bound
      (E.transpose*(A₀-partialMissingCharge A B q α)⁻¹) E (‖α‖*K) ‖α‖ (norm_nonneg _) hf hE
    intro b
    exact (hg b).trans_eq (by ring)
  have hD:∀b,∑b',‖M.toBlocks₂₂ b b'‖≤P:=by
    intro b
    change (∑b',‖partialVacuumDiagonal A B q p b b'‖)≤P
    have he:(∑b',‖partialVacuumDiagonal A B q p b b'‖)=‖if b.val∈A then q⁻¹ else p⁻¹‖:=by
      simp [partialVacuumDiagonal,Matrix.diagonal_apply,apply_ite norm]
    rw [he]
    split_ifs
    · exact hqinv
    · exact hpinv
  refine ⟨hu,?_⟩
  intro b
  rw [hi]
  calc
    _≤∑b',(‖M.toBlocks₂₂ b b'‖+‖(M.toBlocks₂₁*M.toBlocks₁₁⁻¹*M.toBlocks₁₂) b b'‖):=
      Finset.sum_le_sum (fun b' _=>norm_sub_le _ _)
    _=(∑b',‖M.toBlocks₂₂ b b'‖)+∑b',‖(M.toBlocks₂₁*M.toBlocks₁₁⁻¹*M.toBlocks₁₂) b b'‖:=Finset.sum_add_distrib
    _≤_:=add_le_add (hD b) (hprod b)

end LocalLaw
