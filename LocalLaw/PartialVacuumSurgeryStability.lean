import LocalLaw.PartialVacuumNearRows
import LocalLaw.FiniteRankSurgery

/-! # Stability against the explicit partial vacuum benchmark

This algebraic comparison uses no reference class for the switched region.
The new benchmark is the inverse already constructed by eliminating its
retained B leaves and restoring the actual old A boundary deficit.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialVacuumSurgeryStabilityDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {L:Type} [Fintype L] [DecidableEq L]

theorem partialTripleOldPrecision_inverse (A B C:Set L) (A₀:Matrix A A ℂ) (m p α:ℂ)
    (hA:IsUnit A₀) (hm:m≠0) (hp:p≠0) (hrel:p⁻¹=m⁻¹-m*α^2) :
    IsUnit (partialTripleOldPrecision A B C A₀ m p α)∧
      (partialTripleOldPrecision A B C A₀ m p α)⁻¹=
        Matrix.fromBlocks A₀⁻¹ 0 0 (partialSampleCovariance B C m p α) := by
  have hs:=partialSamplePrecision_inverse B C m p α hm hp hrel
  have hb:=blockDiagonal_inverse A₀ (partialSamplePrecision B C m p α) hA hs.1
  exact ⟨hb.1,by simpa only [partialTripleOldPrecision,hs.2] using hb.2⟩

theorem inverse_update_of_difference {I:Type} [Fintype I] [DecidableEq I]
    (A B W:Matrix I I ℂ) (hA:IsUnit A) (hB:IsUnit B) (hW:B-A=W) :
    B⁻¹+B⁻¹*W*A⁻¹=A⁻¹ := by
  have hBmul:B⁻¹*B=1:=Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  have hAmul:A*A⁻¹=1:=Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  rw [←hW]
  calc
    _=B⁻¹+(B⁻¹*B)*A⁻¹-B⁻¹*(A*A⁻¹):=by noncomm_ring
    _=A⁻¹:=by rw [hBmul,hAmul];simp

theorem partialVacuum_surgery_stability (A B C:Set L) (A₀:Matrix A A ℂ) (m p α:ℂ)
    (hA:IsUnit A₀) (hAsym:A₀.IsSymm) (hm:m≠0) (hp:p≠0) (hrel:p⁻¹=m⁻¹-m*α^2)
    (P K δ:ℝ) (hP:0≤P) (hK:0≤K) (hδ:0≤δ)
    (hmnorm:‖m‖≤P) (hpnorm:‖p‖≤P) (ha:‖α*m‖≤1)
    (hrestored:IsUnit (A₀-Matrix.diagonal (fun _:A=>m*α^2)))
    (hrestoredRows:∀ a,∑ a',‖(A₀-Matrix.diagonal (fun _:A=>m*α^2))⁻¹ a a'‖≤K)
    (R T:Matrix (A⊕(B⊕C)) (A⊕(B⊕C)) ℂ)
    (hT:T+R*(partialTripleEdgeUpdate A B C α+partialTripleCharge A B C m α)*T=R)
    (herror:∀ i j,‖(R-(partialTripleOldPrecision A B C A₀ m p α)⁻¹) i j‖≤δ)
    (hsmall:(Fintype.card (A⊕(B⊕C)):ℝ)*
      (1+(P+2*K)*(2*‖α‖+‖m‖*‖α‖^2))*(2*‖α‖+‖m‖*‖α‖^2)*δ≤1/2) :
    ∀ i j,‖(T-(partialTripleNewPrecision A B C A₀ m p α)⁻¹) i j‖≤
      2*(1+(P+2*K)*(2*‖α‖+‖m‖*‖α‖^2))^2*δ := by
  let Old:=partialTripleOldPrecision A B C A₀ m p α
  let New:=partialTripleNewPrecision A B C A₀ m p α
  let W:=partialTripleEdgeUpdate A B C α+partialTripleCharge A B C m α
  have hOld:IsUnit Old:=(partialTripleOldPrecision_inverse A B C A₀ m p α hA hm hp hrel).1
  have hNew:=partialTripleNewPrecision_inverse_rows_cap A B C A₀ m p α hm hp P hP hmnorm hpnorm ha K hK hrestored hrestoredRows
  have hW:New-Old=W:=by
    dsimp only [New,Old,W]
    rw [partialTriple_precision_update A B C A₀ m p α hrel]
    abel
  have hQ:=inverse_update_of_difference Old New W hOld hNew.1 hW
  have hMass:=partialTripleCoupling_mass A B C m α
  have hCol:=partialTripleNewPrecision_inverse_columns_cap A B C A₀ m p α hAsym hm hp P hP hmnorm hpnorm ha K hK hrestored hrestoredRows
  exact surgery_entry_stability R T Old⁻¹ New⁻¹ W hT hQ (P+2*K)
    (2*‖α‖+‖m‖*‖α‖^2) δ (by positivity) (by positivity) hδ hNew.2 hCol hMass.1 hMass.2 herror hsmall

end LocalLaw
