import LocalLaw.BlockSchur

/-!
# Actual arbitrary-set principal deletion

The finite vertex type is genuinely partitioned into T and its complement.
Reindexing commutes with the inverse, so the block identities apply to the
original restricted matrices and Green functions, not just a sum-type model.
-/

namespace LocalLaw

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (T : Set V) [DecidablePred (· ∈ T)]

/-- Reindex a matrix by membership in the retained set and its complement. -/
noncomputable def partitionMatrix (M : Matrix V V ℂ) : Matrix (T ⊕ (Tᶜ : Set V)) (T ⊕ (Tᶜ : Set V)) ℂ :=
  M.submatrix (Equiv.Set.sumCompl T) (Equiv.Set.sumCompl T)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem partitionMatrix11 (M : Matrix V V ℂ) :
    (partitionMatrix T M).toBlocks₁₁ = M.submatrix (Subtype.val : T → V) (Subtype.val : T → V) := by
  ext i j
  simp [partitionMatrix, Matrix.toBlocks₁₁]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem partitionMatrix12 (M : Matrix V V ℂ) :
    (partitionMatrix T M).toBlocks₁₂ = M.submatrix (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) := by
  ext i j
  simp [partitionMatrix, Matrix.toBlocks₁₂]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem partitionMatrix21 (M : Matrix V V ℂ) :
    (partitionMatrix T M).toBlocks₂₁ = M.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V) := by
  ext i j
  simp [partitionMatrix, Matrix.toBlocks₂₁]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem partitionMatrix22 (M : Matrix V V ℂ) :
    (partitionMatrix T M).toBlocks₂₂ = M.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : (Tᶜ : Set V) → V) := by
  ext i j
  simp [partitionMatrix, Matrix.toBlocks₂₂]

/-- Inverse covariance under the actual partition equivalence. -/
theorem partitionMatrix_inverse (M : Matrix V V ℂ) :
    (partitionMatrix T M)⁻¹ = partitionMatrix T M⁻¹ :=
  Matrix.inv_submatrix_equiv M (Equiv.Set.sumCompl T) (Equiv.Set.sumCompl T)

theorem partitionMatrix_isUnit (M : Matrix V V ℂ) (hM : IsUnit M) :
    IsUnit (partitionMatrix T M) :=
  (Matrix.isUnit_submatrix_equiv (Equiv.Set.sumCompl T) (Equiv.Set.sumCompl T)).mpr hM

/-- Actual (A.3), for an arbitrary vertex set T. -/
theorem deleted_principal_inverse (M : Matrix V V ℂ) (hM : IsUnit M)
    (hD : IsUnit (M.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : (Tᶜ : Set V) → V))) :
    (M.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : (Tᶜ : Set V) → V))⁻¹ =
      M⁻¹.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : (Tᶜ : Set V) → V) -
      M⁻¹.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V) *
      (M⁻¹.submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ *
      M⁻¹.submatrix (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) := by
  have hD' : IsUnit (partitionMatrix T M).toBlocks₂₂ := by simpa only [partitionMatrix22] using hD
  have h := deleted_block_inverse (partitionMatrix T M) (partitionMatrix_isUnit T M hM) hD'
  simpa only [partitionMatrix_inverse, partitionMatrix11, partitionMatrix12,
    partitionMatrix21, partitionMatrix22] using h

/-- The retained principal block of the inverse is genuinely invertible. -/
theorem retained_principal_inverse_isUnit (M : Matrix V V ℂ) (hM : IsUnit M)
    (hD : IsUnit (M.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : (Tᶜ : Set V) → V))) :
    IsUnit (M⁻¹.submatrix (Subtype.val : T → V) (Subtype.val : T → V)) := by
  have hD' : IsUnit (partitionMatrix T M).toBlocks₂₂ := by simpa only [partitionMatrix22] using hD
  have h := inverse_block11_isUnit (partitionMatrix T M) (partitionMatrix_isUnit T M hM) hD'
  simpa only [partitionMatrix_inverse, partitionMatrix11] using h

/-- Actual restricted inverse formula (5.8), prior to identifying spectral
cross blocks with the normalized adjacency couplings. -/
theorem retained_principal_inverse (M : Matrix V V ℂ) (hM : IsUnit M)
    (hD : IsUnit (M.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : (Tᶜ : Set V) → V))) :
    (M⁻¹.submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ =
      M.submatrix (Subtype.val : T → V) (Subtype.val : T → V) -
      M.submatrix (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) *
      (M.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : (Tᶜ : Set V) → V))⁻¹ *
      M.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V) := by
  have hD' : IsUnit (partitionMatrix T M).toBlocks₂₂ := by simpa only [partitionMatrix22] using hD
  have h := inverse_inverse_block11 (partitionMatrix T M) (partitionMatrix_isUnit T M hM) hD'
  simpa only [partitionMatrix_inverse, blockSchur, partitionMatrix11, partitionMatrix12,
    partitionMatrix21, partitionMatrix22] using h

/-- Physical arbitrary-set (5.7), with every unit obligation discharged by
Hermitian upper-half-plane resolvent theory. -/
theorem green_deleted_principal (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) :
    green (H.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : (Tᶜ : Set V) → V)) z =
      (green H z).submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : (Tᶜ : Set V) → V) -
      (green H z).submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V) *
      ((green H z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ *
      (green H z).submatrix (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) := by
  have hD := principal_spectralMatrix_isUnit H hH z hz
    (Subtype.val : (Tᶜ : Set V) → V) Subtype.val_injective
  have h := deleted_principal_inverse T (spectralMatrix H z) (spectralMatrix_isUnit H hH z hz) hD
  rw [← spectralMatrix_principal H z (Subtype.val : (Tᶜ : Set V) → V) Subtype.val_injective] at h
  exact h

omit [Fintype V] [DecidablePred (· ∈ T)] in
/-- The scalar spectral shift vanishes on disjoint off-diagonal blocks. -/
theorem spectralMatrix_cross12 (H : Matrix V V ℂ) (z : ℂ) :
    (spectralMatrix H z).submatrix (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) =
      H.submatrix (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) := by
  ext i j
  have hne : (i : V) ≠ (j : V) := by
    intro heq
    exact j.property (heq ▸ i.property)
  simp [spectralMatrix, Matrix.one_apply, hne]

omit [Fintype V] [DecidablePred (· ∈ T)] in
theorem spectralMatrix_cross21 (H : Matrix V V ℂ) (z : ℂ) :
    (spectralMatrix H z).submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V) =
      H.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V) := by
  ext i j
  have hne : (i : V) ≠ (j : V) := by
    intro heq
    exact i.property (heq.symm ▸ j.property)
  simp [spectralMatrix, Matrix.one_apply, hne]

/-- Physical actual-set (5.8), with normalized adjacency coupling blocks. -/
theorem green_retained_principal_inverse (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) :
    IsUnit ((green H z).submatrix (Subtype.val : T → V) (Subtype.val : T → V)) ∧
    ((green H z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ =
      spectralMatrix (H.submatrix (Subtype.val : T → V) (Subtype.val : T → V)) z -
      H.submatrix (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) *
      green (H.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : (Tᶜ : Set V) → V)) z *
      H.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V) := by
  have hD := principal_spectralMatrix_isUnit H hH z hz
    (Subtype.val : (Tᶜ : Set V) → V) Subtype.val_injective
  have hM := spectralMatrix_isUnit H hH z hz
  refine ⟨retained_principal_inverse_isUnit T (spectralMatrix H z) hM hD, ?_⟩
  have h := retained_principal_inverse T (spectralMatrix H z) hM hD
  rw [spectralMatrix_cross12, spectralMatrix_cross21,
    ← spectralMatrix_principal H z (Subtype.val : T → V) Subtype.val_injective,
    ← spectralMatrix_principal H z (Subtype.val : (Tᶜ : Set V) → V) Subtype.val_injective] at h
  exact h

end LocalLaw
