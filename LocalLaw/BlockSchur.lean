import LocalLaw.FiniteModel

/-!
# Genuine block Schur identities for finite resolvents

This supplies (A.3), (5.7) and (5.8) with explicit nonsingularity obligations.
For a nonsingular block matrix with nonsingular deleted principal block, the
Schur complement and the corresponding inverse block are proved nonsingular.
-/

namespace LocalLaw

section Blocks

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The Schur complement of the lower-right block. -/
noncomputable def blockSchur (M : Matrix (I ⊕ J) (I ⊕ J) ℂ) : Matrix I I ℂ :=
  M.toBlocks₁₁ - M.toBlocks₁₂ * M.toBlocks₂₂⁻¹ * M.toBlocks₂₁

/-- Invertibility of the full matrix and the deleted block imply
invertibility of the Schur complement. -/
theorem blockSchur_isUnit (M : Matrix (I ⊕ J) (I ⊕ J) ℂ)
    (hM : IsUnit M) (hD : IsUnit M.toBlocks₂₂) : IsUnit (blockSchur M) := by
  letI : Invertible M.toBlocks₂₂ := Classical.choice hD.nonempty_invertible
  have hfull : IsUnit (Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂) := by
    rw [Matrix.fromBlocks_toBlocks]
    exact hM
  have h := Matrix.isUnit_fromBlocks_iff_of_invertible₂₂.mp hfull
  simpa only [blockSchur, Matrix.invOf_eq_nonsing_inv] using h

/-- The complete inverse formula around a nonsingular deleted block. -/
theorem block_inverse_formula (M : Matrix (I ⊕ J) (I ⊕ J) ℂ)
    (hM : IsUnit M) (hD : IsUnit M.toBlocks₂₂) :
    M⁻¹ = Matrix.fromBlocks (blockSchur M)⁻¹
      (-((blockSchur M)⁻¹ * M.toBlocks₁₂ * M.toBlocks₂₂⁻¹))
      (-(M.toBlocks₂₂⁻¹ * M.toBlocks₂₁ * (blockSchur M)⁻¹))
      (M.toBlocks₂₂⁻¹ + M.toBlocks₂₂⁻¹ * M.toBlocks₂₁ *
        (blockSchur M)⁻¹ * M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) := by
  letI : Invertible M.toBlocks₂₂ := Classical.choice hD.nonempty_invertible
  have hS : IsUnit (M.toBlocks₁₁ - M.toBlocks₁₂ * ⅟ M.toBlocks₂₂ * M.toBlocks₂₁) := by
    simpa only [Matrix.invOf_eq_nonsing_inv, blockSchur] using blockSchur_isUnit M hM hD
  letI : Invertible (M.toBlocks₁₁ - M.toBlocks₁₂ * ⅟ M.toBlocks₂₂ * M.toBlocks₂₁) :=
    Classical.choice hS.nonempty_invertible
  letI := Matrix.fromBlocks₂₂Invertible M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂
  have h := Matrix.invOf_fromBlocks₂₂_eq M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂
  simpa only [Matrix.invOf_eq_nonsing_inv, Matrix.fromBlocks_toBlocks, blockSchur] using h

/-- The upper inverse block is the inverse Schur complement. -/
theorem inverse_block11 (M : Matrix (I ⊕ J) (I ⊕ J) ℂ)
    (hM : IsUnit M) (hD : IsUnit M.toBlocks₂₂) :
    (M⁻¹).toBlocks₁₁ = (blockSchur M)⁻¹ := by
  rw [block_inverse_formula M hM hD]
  rfl

/-- The corresponding lower inverse block, using a nonsingular upper block. -/
theorem inverse_block22 (M : Matrix (I ⊕ J) (I ⊕ J) ℂ)
    (hM : IsUnit M) (hA : IsUnit M.toBlocks₁₁) :
    IsUnit (M.toBlocks₂₂ - M.toBlocks₂₁ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂) ∧
    (M⁻¹).toBlocks₂₂ = (M.toBlocks₂₂ - M.toBlocks₂₁ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂)⁻¹ := by
  letI : Invertible M.toBlocks₁₁ := Classical.choice hA.nonempty_invertible
  have hfull : IsUnit (Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂) := by
    rw [Matrix.fromBlocks_toBlocks]
    exact hM
  have hS := Matrix.isUnit_fromBlocks_iff_of_invertible₁₁.mp hfull
  letI : Invertible (M.toBlocks₂₂ - M.toBlocks₂₁ * ⅟ M.toBlocks₁₁ * M.toBlocks₁₂) :=
    Classical.choice hS.nonempty_invertible
  letI := Matrix.fromBlocks₁₁Invertible M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂
  have h := Matrix.invOf_fromBlocks₁₁_eq M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂
  have hentry := congrArg Matrix.toBlocks₂₂ h
  constructor
  · simpa only [Matrix.invOf_eq_nonsing_inv] using hS
  · simpa only [Matrix.invOf_eq_nonsing_inv, Matrix.fromBlocks_toBlocks,
      Matrix.toBlocks_fromBlocks₂₂] using hentry

/-- The inverse block itself is nonsingular. This is a conclusion, not an
extra hypothesis about a principal block of an arbitrary inverse. -/
theorem inverse_block11_isUnit (M : Matrix (I ⊕ J) (I ⊕ J) ℂ)
    (hM : IsUnit M) (hD : IsUnit M.toBlocks₂₂) : IsUnit (M⁻¹).toBlocks₁₁ := by
  rw [inverse_block11 M hM hD]
  exact Matrix.isUnit_nonsing_inv_iff.mpr (blockSchur_isUnit M hM hD)

/-- Formula (5.8): inverse of the retained Green block equals the Schur
complement of the original matrix. -/
theorem inverse_inverse_block11 (M : Matrix (I ⊕ J) (I ⊕ J) ℂ)
    (hM : IsUnit M) (hD : IsUnit M.toBlocks₂₂) :
    (M⁻¹).toBlocks₁₁⁻¹ = blockSchur M := by
  rw [inverse_block11 M hM hD]
  exact Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (blockSchur_isUnit M hM hD))

/-- Formula (A.3)/(5.7): recover the deleted-block resolvent from the blocks
of the full inverse. Every matrix inverse used here is justified. -/
theorem deleted_block_inverse (M : Matrix (I ⊕ J) (I ⊕ J) ℂ)
    (hM : IsUnit M) (hD : IsUnit M.toBlocks₂₂) :
    M.toBlocks₂₂⁻¹ = (M⁻¹).toBlocks₂₂ - (M⁻¹).toBlocks₂₁ *
      (M⁻¹).toBlocks₁₁⁻¹ * (M⁻¹).toBlocks₁₂ := by
  have hG : IsUnit M⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hM
  have hG11 := inverse_block11_isUnit M hM hD
  obtain ⟨hS, hidentity⟩ := inverse_block22 M⁻¹ hG hG11
  rw [Matrix.nonsing_inv_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hM)] at hidentity
  have hinv := congrArg (fun A : Matrix J J ℂ => A⁻¹) hidentity
  dsimp only at hinv
  rw [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS)] at hinv
  exact hinv

end Blocks

section PhysicalResolvents

variable {V U I J : Type*} [Fintype V] [DecidableEq V]
variable [Fintype U] [DecidableEq U]

omit [Fintype V] [Fintype U] in
/-- Spectral shifting commutes with an injective principal restriction. -/
theorem spectralMatrix_principal (H : Matrix V V ℂ) (z : ℂ)
    (f : U → V) (hf : Function.Injective f) :
    spectralMatrix (H.submatrix f f) z = (spectralMatrix H z).submatrix f f := by
  ext i j
  simp [spectralMatrix, Matrix.one_apply, hf.eq_iff]

omit [Fintype V] in
/-- Every actual principal spectral block is nonsingular in the upper half
plane. No probabilistic regularity hypothesis is needed. -/
theorem principal_spectralMatrix_isUnit (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (f : U → V) (hf : Function.Injective f) :
    IsUnit ((spectralMatrix H z).submatrix f f) := by
  rw [← spectralMatrix_principal H z f hf]
  exact spectralMatrix_isUnit _ (hH.submatrix f) z hz

variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Physical (5.7) for any block decomposition of a Hermitian matrix. -/
theorem green_deleted_block (H : Matrix (I ⊕ J) (I ⊕ J) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) :
    (spectralMatrix H z).toBlocks₂₂⁻¹ = (green H z).toBlocks₂₂ -
      (green H z).toBlocks₂₁ * (green H z).toBlocks₁₁⁻¹ * (green H z).toBlocks₁₂ := by
  have hD : IsUnit (spectralMatrix H z).toBlocks₂₂ :=
    principal_spectralMatrix_isUnit H hH z hz Sum.inr Sum.inr_injective
  exact deleted_block_inverse (spectralMatrix H z) (spectralMatrix_isUnit H hH z hz) hD

/-- Physical (5.8), with invertibility of the retained Green block derived
from Hermitian resolvent nonsingularity. -/
theorem green_retained_block_inverse (H : Matrix (I ⊕ J) (I ⊕ J) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) :
    IsUnit (green H z).toBlocks₁₁ ∧ (green H z).toBlocks₁₁⁻¹ = blockSchur (spectralMatrix H z) := by
  have hM := spectralMatrix_isUnit H hH z hz
  have hD : IsUnit (spectralMatrix H z).toBlocks₂₂ :=
    principal_spectralMatrix_isUnit H hH z hz Sum.inr Sum.inr_injective
  exact ⟨inverse_block11_isUnit _ hM hD, inverse_inverse_block11 _ hM hD⟩

end PhysicalResolvents

end LocalLaw
