import LocalLaw.PartialLMaskVacuum

/-! # Exact L-mask partial vacuum update and its finite coupling mass -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialLMaskSurgeryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {L : Type} [Fintype L] [DecidableEq L]

def partialLMaskCharge (A B C Lmask : Set L) (q α : ℂ) : Matrix (A⊕(B⊕C)) (A⊕(B⊕C)) ℂ :=
  Matrix.diagonal (fun u=>match u with
    | .inl a=>q*α^2*((if a.val∈B then 1 else 0)-(if a.val∈Lmask then 1 else 0))
    | .inr (.inl b)=>q*α^2*((if b.val∈A then 1 else 0)-(if b.val∈C then 1 else 0))
    | .inr (.inr c)=>q*α^2*((if c.val∈Lmask then 1 else 0)-(if c.val∈B then 1 else 0)))

omit [Fintype L] in
theorem partialLMask_precision_update (A B C Lmask : Set L) (A0 : Matrix A A ℂ) (q p α : ℂ)
    (hrel : p⁻¹=q⁻¹-q*α^2) :
    partialLMaskNewPrecision A B C Lmask A0 q p α=
      partialTripleOldPrecision A B C A0 q p α+partialTripleEdgeUpdate A B C α+
        partialLMaskCharge A B C Lmask q α := by
  ext u v
  rcases u with a|(b|c) <;> rcases v with a'|(b'|c')
  all_goals simp only [partialLMaskNewPrecision,partialTripleOldPrecision,partialTripleEdgeUpdate,
    partialLMaskCharge,partialLMaskShift,partialLMaskCPrecision,partialMissingCharge,partialSamplePrecision,
    partialVacuumDiagonal,Matrix.submatrix_apply,Equiv.sumAssoc_symm_apply_inl,
    Equiv.sumAssoc_symm_apply_inr_inl,Equiv.sumAssoc_symm_apply_inr_inr,
    Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
    Matrix.add_apply,Matrix.sub_apply,Matrix.diagonal_apply,Matrix.zero_apply,Matrix.transpose_apply,
    partialMatchingCoupling]
  all_goals first | rfl | simp only [Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq,if_false,add_zero,zero_add,sub_zero]
  all_goals try { split_ifs <;> simp_all [hrel] <;> ring }

theorem partialLMaskCharge_rows (A B C Lmask : Set L) (q α : ℂ) (u : A⊕(B⊕C)) :
    (∑v,‖partialLMaskCharge A B C Lmask q α u v‖)≤‖q‖*‖α‖^2 := by
  have hd {X:Type}[Fintype X][DecidableEq X] (f:X→ℂ) (x:X) :
      (∑y,‖Matrix.diagonal f x y‖)=‖f x‖ := by simp [Matrix.diagonal_apply,apply_ite norm]
  unfold partialLMaskCharge
  rw [hd]
  rcases u with a|(b|c)
  all_goals dsimp only
  all_goals split_ifs <;> simp [norm_mul,norm_pow] <;> (try positivity)

omit [Fintype L] in
theorem partialLMaskCoupling_isSymm (A B C Lmask : Set L) (q α : ℂ) :
    (partialTripleEdgeUpdate A B C α+partialLMaskCharge A B C Lmask q α).IsSymm := by
  have he : (partialTripleEdgeUpdate A B C α).IsSymm := by
    have hh:=(partialTripleCoupling_isSymm A B C q α).sub
      (show (partialTripleCharge A B C q α).IsSymm from Matrix.isSymm_diagonal _)
    simpa only [add_sub_cancel_right] using hh
  exact he.add (Matrix.isSymm_diagonal _)

theorem partialLMaskCoupling_mass (A B C Lmask : Set L) (q α : ℂ) :
    let W:=partialTripleEdgeUpdate A B C α+partialLMaskCharge A B C Lmask q α
    (∀u,∑v,‖W u v‖≤2*‖α‖+‖q‖*‖α‖^2) ∧
      (∀v,∑u,‖W u v‖≤2*‖α‖+‖q‖*‖α‖^2) := by
  dsimp only
  have hr (u:A⊕(B⊕C)) : (∑v,‖(partialTripleEdgeUpdate A B C α+partialLMaskCharge A B C Lmask q α) u v‖)≤
      2*‖α‖+‖q‖*‖α‖^2 :=
    (Finset.sum_le_sum (fun v _=>norm_add_le _ _)).trans
      ((Finset.sum_add_distrib).trans_le (add_le_add
        (partialTripleEdgeUpdate_rows A B C α u) (partialLMaskCharge_rows A B C Lmask q α u)))
  refine ⟨hr,fun v=>?_⟩
  have hs:=partialLMaskCoupling_isSymm A B C Lmask q α
  simpa only [hs.apply] using hr v

end LocalLaw
