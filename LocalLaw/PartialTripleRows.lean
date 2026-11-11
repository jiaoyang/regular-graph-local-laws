import LocalLaw.PartialTripleSurgery
import LocalLaw.PartialSurgeryCoupling

/-! # Uniform rows and columns for the exact partial vacuum surgery -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialTripleRowsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {L:Type} [Fintype L] [DecidableEq L]

theorem partialTripleEdgeUpdate_rows (A B C:Set L) (α:ℂ) (u:A⊕(B⊕C)) :
    (∑ v,‖partialTripleEdgeUpdate A B C α u v‖)≤2*‖α‖ := by
  rcases u with a | (b | c)
  · simp only [Fintype.sum_sum_type,partialTripleEdgeUpdate,norm_zero,Finset.sum_const_zero,zero_add,add_zero]
    exact (partialMatching_row_sum A B α a).trans (by nlinarith [norm_nonneg α])
  · simp only [Fintype.sum_sum_type,partialTripleEdgeUpdate,norm_zero,norm_neg,Finset.sum_const_zero,zero_add]
    exact (add_le_add (partialMatching_row_sum B A α b) (partialMatching_row_sum B C α b)).trans_eq (by ring)
  · simp only [Fintype.sum_sum_type,partialTripleEdgeUpdate,norm_zero,norm_neg,Finset.sum_const_zero,zero_add,add_zero]
    exact (partialMatching_row_sum C B α c).trans (by nlinarith [norm_nonneg α])

theorem partialTripleCharge_rows (A B C:Set L) (m α:ℂ) (u:A⊕(B⊕C)) :
    (∑ v,‖partialTripleCharge A B C m α u v‖)≤‖m‖*‖α‖^2 := by
  have hh {X:Type} [Fintype X] [DecidableEq X] (f:X→ℂ) (x:X) :
      (∑ y,‖Matrix.diagonal f x y‖)=‖f x‖:=by
    simp [Matrix.diagonal_apply,apply_ite norm]
  unfold partialTripleCharge
  rw [hh]
  rcases u with a | (b | c)
  all_goals dsimp only
  all_goals split_ifs <;> simp [norm_mul,norm_pow] <;> (try positivity)

omit [Fintype L] in

theorem partialTripleCoupling_isSymm (A B C:Set L) (m α:ℂ) :
    (partialTripleEdgeUpdate A B C α+partialTripleCharge A B C m α).IsSymm := by
  have he:(partialTripleEdgeUpdate A B C α).IsSymm:=by
    ext u v
    rcases u with a | (b | c) <;> rcases v with a' | (b' | c') <;>
      simp [Matrix.transpose_apply,partialTripleEdgeUpdate,partialMatchingCoupling,eq_comm]
  have hd:(partialTripleCharge A B C m α).IsSymm:=Matrix.isSymm_diagonal _
  exact he.add hd

theorem partialTripleCoupling_mass (A B C:Set L) (m α:ℂ) :
    let W:=partialTripleEdgeUpdate A B C α+partialTripleCharge A B C m α
    (∀ u,∑ v,‖W u v‖≤2*‖α‖+‖m‖*‖α‖^2)∧
      (∀ v,∑ u,‖W u v‖≤2*‖α‖+‖m‖*‖α‖^2) := by
  dsimp only
  have hrow (u:A⊕(B⊕C)) : (∑ v,‖(partialTripleEdgeUpdate A B C α+partialTripleCharge A B C m α) u v‖)≤_ :=
    (Finset.sum_le_sum (fun v _=>norm_add_le _ _)).trans
      ((Finset.sum_add_distrib).trans_le
        (add_le_add (partialTripleEdgeUpdate_rows A B C α u) (partialTripleCharge_rows A B C m α u)))
  refine ⟨hrow,fun v=>?_⟩
  have hs:=partialTripleCoupling_isSymm A B C m α
  have heq:(∑ u,‖(partialTripleEdgeUpdate A B C α+partialTripleCharge A B C m α) u v‖)=
      ∑ u,‖(partialTripleEdgeUpdate A B C α+partialTripleCharge A B C m α) v u‖:=
    Finset.sum_congr rfl (fun u _=>congrArg norm (hs.apply v u))
  rw [heq]
  exact hrow v

omit [Fintype L] in
theorem partialTripleNewPrecision_isSymm (A B C:Set L) (A₀:Matrix A A ℂ) (m p α:ℂ)
    (hA:A₀.IsSymm) : (partialTripleNewPrecision A B C A₀ m p α).IsSymm := by
  have hM:(Matrix.fromBlocks (A₀-partialMissingCharge A B m α)
      (partialMatchingCoupling A B α) (partialMatchingCoupling A B α).transpose
      (partialVacuumDiagonal A B m p)).IsSymm:=by
    change A₀.transpose=A₀ at hA
    simp only [Matrix.IsSymm,Matrix.fromBlocks_transpose,Matrix.transpose_sub,
      partialMissingCharge,partialVacuumDiagonal,Matrix.diagonal_transpose,
      Matrix.transpose_transpose,hA]
  have hF:(Matrix.fromBlocks
      (Matrix.fromBlocks (A₀-partialMissingCharge A B m α)
        (partialMatchingCoupling A B α) (partialMatchingCoupling A B α).transpose
        (partialVacuumDiagonal A B m p)) 0 0 (Matrix.diagonal (fun _:C=>m⁻¹))).IsSymm:=by
    simp only [Matrix.IsSymm,Matrix.fromBlocks_transpose,Matrix.transpose_zero,
      Matrix.diagonal_transpose,hM.eq]
  ext u v
  exact hF.apply _ _

theorem partialTripleNewPrecision_inverse_columns (A B C:Set L) (A₀:Matrix A A ℂ) (m p α:ℂ)
    (hA:A₀.IsSymm) (hm:m≠0) (hp:p≠0) (hmnorm:‖m‖≤1) (hpnorm:‖p‖≤2) (ha:‖α*m‖≤1)
    (K:ℝ) (hK:0≤K)
    (hrestored:IsUnit (A₀-Matrix.diagonal (fun _:A=>m*α^2)))
    (hrows:∀ a,∑ a',‖(A₀-Matrix.diagonal (fun _:A=>m*α^2))⁻¹ a a'‖≤K) :
    ∀ v,∑ u,‖(partialTripleNewPrecision A B C A₀ m p α)⁻¹ u v‖≤2+2*K := by
  have hs:((partialTripleNewPrecision A B C A₀ m p α)⁻¹).IsSymm:=by
    change ((partialTripleNewPrecision A B C A₀ m p α)⁻¹).transpose=_
    rw [Matrix.transpose_nonsing_inv,(partialTripleNewPrecision_isSymm A B C A₀ m p α hA).eq]
  intro v
  have heq:(∑ u,‖(partialTripleNewPrecision A B C A₀ m p α)⁻¹ u v‖)=
      ∑ u,‖(partialTripleNewPrecision A B C A₀ m p α)⁻¹ v u‖:=
    Finset.sum_congr rfl (fun u _=>congrArg norm (hs.apply v u))
  rw [heq]
  exact (partialTripleNewPrecision_inverse_rows A B C A₀ m p α hm hp hmnorm hpnorm ha K hK hrestored hrows).2 v

end LocalLaw
