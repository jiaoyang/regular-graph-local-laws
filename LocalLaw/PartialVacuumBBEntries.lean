import LocalLaw.PartialVacuumBInverse

/-! # Sampled-first off-diagonals inherit the separated restored-A kernel -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialVacuumBBEntriesDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {L:Type} [Fintype L] [DecidableEq L]

theorem partialVacuum_BGreen_formula (A B:Set L)(A₀:Matrix A A ℂ)(q p α:ℂ)
    (hq:q≠0)(hp:p≠0)(hr:IsUnit (A₀-Matrix.diagonal (fun _:A=>q*α^2))) :
    let E:=partialMatchingCoupling A B α
    let M:=Matrix.fromBlocks (A₀-partialMissingCharge A B q α) E E.transpose (partialVacuumDiagonal A B q p)
    (M⁻¹).toBlocks₂₂=partialVacuumInverse A B q p+
      partialMatchingCoupling B A (α*q)*(A₀-Matrix.diagonal (fun _:A=>q*α^2))⁻¹*
        partialMatchingCoupling A B (α*q) := by
  dsimp only
  let E:=partialMatchingCoupling A B α
  let D:=partialVacuumDiagonal A B q p
  let M:=Matrix.fromBlocks (A₀-partialMissingCharge A B q α) E E.transpose D
  have hv:=partialVacuum_schur A B A₀ q p α hq hp hr
  have hM:IsUnit M:=hv.1
  obtain ⟨hD,hDi⟩:=partialVacuumDiagonal_inverse A B q p hq hp
  have hSi:(blockSchur M)⁻¹=(A₀-Matrix.diagonal (fun _:A=>q*α^2))⁻¹:=by
    rw [←inverse_block11 M hM hD]
    exact hv.2
  have hh:=congrArg Matrix.toBlocks₂₂ (block_inverse_formula M hM hD)
  dsimp only [Matrix.toBlocks_fromBlocks₂₂] at hh
  change (M⁻¹).toBlocks₂₂=D⁻¹+D⁻¹*E.transpose*(blockSchur M)⁻¹*E*D⁻¹ at hh
  rw [hSi,hDi] at hh
  have hprod:=partialMatching_vacuum_products A B q p α
  calc
    _=partialVacuumInverse A B q p+
        (partialVacuumInverse A B q p*E.transpose)*
          (A₀-Matrix.diagonal (fun _:A=>q*α^2))⁻¹*(E*partialVacuumInverse A B q p):=by
      rw [hh]
      simp only [Matrix.mul_assoc]
    _=_:=by rw [hprod.1,hprod.2]

theorem partialMatching_sandwich_offdiagonal (A B:Set L)(P:Matrix A A ℂ)(β:ℂ)
    (τ:ℝ)(hτ:0≤τ)(hoff:∀a a',a≠a'→‖P a a'‖≤τ)(b b':B)(hbb:b≠b') :
    ‖(partialMatchingCoupling B A β*P*partialMatchingCoupling A B β) b b'‖≤‖β‖^2*τ := by
  let F:=partialMatchingCoupling B A β
  let E:=partialMatchingCoupling A B β
  let Poff:=P-Matrix.diagonal (fun a=>P a a)
  have hp:∀a a',‖Poff a a'‖≤τ:=by
    intro a a'
    by_cases he:a=a'
    · subst a';simpa only [Poff,Matrix.sub_apply,Matrix.diagonal_apply_eq,sub_self,norm_zero] using hτ
    · simpa only [Poff,Matrix.sub_apply,Matrix.diagonal_apply_ne _ he,sub_zero] using hoff a a' he
  have heq:(F*P*E) b b'=(F*Poff*E) b b':=by
    simp only [Matrix.mul_apply,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a' _
    apply Finset.sum_congr rfl
    intro a _
    by_cases haa:a=a'
    · subst a'
      have hnot:b.val≠b'.val:=fun h=>hbb (Subtype.ext h)
      by_cases hba:b.val=a.val
      · have hab:a.val≠b'.val:=fun h=>hnot (hba.trans h)
        simp [E,partialMatchingCoupling,hab]
      · simp [F,partialMatchingCoupling,hba]
    · simp only [Poff,Matrix.sub_apply,Matrix.diagonal_apply_ne _ haa,sub_zero]
  rw [heq]
  have hleft:∀a',‖(F*Poff) b a'‖≤‖β‖*τ:=fun a'=>
    rectangular_product_row_bound F Poff b a' ‖β‖ τ hτ (partialMatching_row_sum B A β b) (fun a=>hp a a')
  have hcol:(∑a:A,‖E a b'‖)≤‖β‖:=by
    have he:E.transpose=partialMatchingCoupling B A β:=by
      ext k a
      simp only [E,Matrix.transpose_apply,partialMatchingCoupling,eq_comm]
    have hh:=partialMatching_row_sum B A β b'
    rw [←he] at hh
    exact hh
  exact (rectangular_product_column_bound (F*Poff) E b b' (‖β‖*τ) ‖β‖
    (by positivity) hleft hcol).trans_eq (by ring)

theorem partialVacuum_BGreen_offdiagonal (A B:Set L)(A₀:Matrix A A ℂ)(q p α:ℂ)
    (hq:q≠0)(hp:p≠0)(hr:IsUnit (A₀-Matrix.diagonal (fun _:A=>q*α^2)))
    (τ:ℝ)(hτ:0≤τ)
    (hoff:∀a a',a≠a'→‖(A₀-Matrix.diagonal (fun _:A=>q*α^2))⁻¹ a a'‖≤τ)
    (b b':B)(hbb:b≠b') :
    let E:=partialMatchingCoupling A B α
    let M:=Matrix.fromBlocks (A₀-partialMissingCharge A B q α) E E.transpose (partialVacuumDiagonal A B q p)
    ‖(M⁻¹).toBlocks₂₂ b b'‖≤‖α*q‖^2*τ := by
  dsimp only
  rw [partialVacuum_BGreen_formula A B A₀ q p α hq hp hr]
  simp only [Matrix.add_apply,partialVacuumInverse,Matrix.diagonal_apply_ne _ hbb,zero_add]
  exact partialMatching_sandwich_offdiagonal A B _ (α*q) τ hτ hoff b b' hbb

end LocalLaw
