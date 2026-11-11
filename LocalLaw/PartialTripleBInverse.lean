import LocalLaw.PartialVacuumBInverse
import LocalLaw.DiagonalSchurComparison

/-! # Sampled-first inverse blocks in the full partial-triple benchmark

The detached C block does not change B. Symmetry supplies inverse columns;
the actual retained B inverse then follows from a proved covariance error.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialTripleBInverseDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {L:Type} [Fintype L] [DecidableEq L]

theorem partialTriple_BGreen_eq (A B C:Set L)(A₀:Matrix A A ℂ)(q p α:ℂ)
    (hq:q≠0)(hp:p≠0)(hrestored:IsUnit (A₀-Matrix.diagonal (fun _:A=>q*α^2))) :
    let E:=partialMatchingCoupling A B α
    let M:=Matrix.fromBlocks (A₀-partialMissingCharge A B q α) E E.transpose (partialVacuumDiagonal A B q p)
    ((partialTripleNewPrecision A B C A₀ q p α)⁻¹).submatrix
      (fun b:B=>Sum.inr (Sum.inl b)) (fun b:B=>Sum.inr (Sum.inl b))=(M⁻¹).toBlocks₂₂ := by
  dsimp only
  let E:=partialMatchingCoupling A B α
  let M:=Matrix.fromBlocks (A₀-partialMissingCharge A B q α) E E.transpose (partialVacuumDiagonal A B q p)
  let D:Matrix C C ℂ:=Matrix.diagonal (fun _=>q⁻¹)
  have hM:IsUnit M:=(partialVacuum_schur A B A₀ q p α hq hp hrestored).1
  have hD:IsUnit D:=(scalar_diagonal_inverse (I:=C) q⁻¹ (inv_ne_zero hq)).1
  have hh:=blockDiagonal_inverse M D hM hD
  unfold partialTripleNewPrecision
  rw [Matrix.inv_submatrix_equiv,hh.2]
  rfl

theorem partialTriple_BGreen_inverse_rows_cols (A B C:Set L)(A₀:Matrix A A ℂ)(q p α:ℂ)
    (hsym:A₀.IsSymm)(hq:q≠0)(hp:p≠0)(P K:ℝ)(hP:0≤P)(hK:0≤K)
    (hqinv:‖q⁻¹‖≤P)(hpinv:‖p⁻¹‖≤P)
    (hrestored:IsUnit (A₀-Matrix.diagonal (fun _:A=>q*α^2)))
    (hmissing:IsUnit (A₀-partialMissingCharge A B q α))
    (hrows:∀a,∑a',‖(A₀-partialMissingCharge A B q α)⁻¹ a a'‖≤K) :
    let Q:=((partialTripleNewPrecision A B C A₀ q p α)⁻¹).submatrix
      (fun b:B=>Sum.inr (Sum.inl b)) (fun b:B=>Sum.inr (Sum.inl b))
    IsUnit Q ∧ (∀b,∑b',‖Q⁻¹ b b'‖≤P+‖α‖^2*K) ∧
      (∀b',∑b,‖Q⁻¹ b b'‖≤P+‖α‖^2*K) := by
  dsimp only
  rw [partialTriple_BGreen_eq A B C A₀ q p α hq hp hrestored]
  let E:=partialMatchingCoupling A B α
  let M:=Matrix.fromBlocks (A₀-partialMissingCharge A B q α) E E.transpose (partialVacuumDiagonal A B q p)
  have hb:=partialVacuum_BGreen_inverse_rows A B A₀ q p α hq hp P K hP hK hqinv hpinv hrestored hmissing hrows
  have hMs:M.transpose=M:=by
    change A₀.transpose=A₀ at hsym
    simp only [M,Matrix.fromBlocks_transpose,Matrix.transpose_sub,partialMissingCharge,
      partialVacuumDiagonal,Matrix.diagonal_transpose,Matrix.transpose_transpose,hsym]
  have hQs:(M⁻¹).toBlocks₂₂.IsSymm:=by
    have hMi:M⁻¹.IsSymm:=by
      change M⁻¹.transpose=M⁻¹
      rw [Matrix.transpose_nonsing_inv,hMs]
    exact hMi.submatrix Sum.inr
  have hQis:(M⁻¹).toBlocks₂₂⁻¹.IsSymm:=by
    change ((M⁻¹).toBlocks₂₂⁻¹).transpose=(M⁻¹).toBlocks₂₂⁻¹
    rw [Matrix.transpose_nonsing_inv,hQs]
  refine ⟨hb.1,hb.2,?_⟩
  intro b
  change (∑b',‖(M⁻¹).toBlocks₂₂⁻¹ b' b‖)≤_
  calc
    _=∑b',‖(M⁻¹).toBlocks₂₂⁻¹ b b'‖:=
      Finset.sum_congr rfl (fun b' _=>congrArg norm (hQis.apply b b'))
    _≤_:=hb.2 b

theorem partialTriple_BGreen_inverse_stability (A B C:Set L)(A₀:Matrix A A ℂ)(q p α:ℂ)
    (hsym:A₀.IsSymm)(hq:q≠0)(hp:p≠0)(P K σ:ℝ)(hP:0≤P)(hK:0≤K)(hσ:0≤σ)
    (hqinv:‖q⁻¹‖≤P)(hpinv:‖p⁻¹‖≤P)
    (hrestored:IsUnit (A₀-Matrix.diagonal (fun _:A=>q*α^2)))
    (hmissing:IsUnit (A₀-partialMissingCharge A B q α))
    (hrows:∀a,∑a',‖(A₀-partialMissingCharge A B q α)⁻¹ a a'‖≤K)
    (U:Matrix B B ℂ)(hU:IsUnit U)
    (herr:∀b b',‖U b b'-((partialTripleNewPrecision A B C A₀ q p α)⁻¹)
      (.inr (.inl b)) (.inr (.inl b'))‖≤σ)
    (hsmall:(Fintype.card B:ℝ)*(P+‖α‖^2*K)*σ≤1/2) :
    (∀b,∑b',‖U⁻¹ b b'‖≤2*(P+‖α‖^2*K)) ∧
      (∀b',∑b,‖U⁻¹ b b'‖≤2*(P+‖α‖^2*K)) := by
  have hh:=partialTriple_BGreen_inverse_rows_cols A B C A₀ q p α hsym hq hp P K hP hK
    hqinv hpinv hrestored hmissing hrows
  exact inverse_row_column_stability U _ hU hh.1 (P+‖α‖^2*K) σ (by positivity) hσ hh.2.1 hh.2.2 herr hsmall

end LocalLaw
