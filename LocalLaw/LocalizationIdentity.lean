import LocalLaw.ComponentModel

/-!
# Genuine finite-model localization identity

Restricting a deficient model adds exactly the missing incident edges to its
boundary coefficient. The difference of the restricted and full inverse is
therefore the actual Schur boundary self-energy error, rather than an assumed
localization estimate. All matrix units below are derived from the physical
upper-half-plane conditions.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance localizationIdentityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Algebra
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem matrix_inverse_difference (A B : Matrix V V ℂ) (hA : IsUnit A) (hB : IsUnit B) :
    A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
  have hAA := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hBB := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  rw [mul_sub, sub_mul, Matrix.mul_assoc, hBB, Matrix.mul_one, hAA, Matrix.one_mul]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype V] [DecidableEq V] in
theorem block_localization_identity (M : Matrix (I ⊕ J) (I ⊕ J) ℂ)
    (W : Matrix I I ℂ) (hM : IsUnit M) (hD : IsUnit M.toBlocks₂₂)
    (hP : IsUnit (M.toBlocks₁₁ - W)) :
    (M.toBlocks₁₁ - W)⁻¹ - (M⁻¹).toBlocks₁₁ =
      (M.toBlocks₁₁ - W)⁻¹ * (W - M.toBlocks₁₂ * M.toBlocks₂₂⁻¹ * M.toBlocks₂₁) *
        (M⁻¹).toBlocks₁₁ := by
  rw [inverse_block11 M hM hD,
    matrix_inverse_difference (M.toBlocks₁₁ - W) (blockSchur M) hP (blockSchur_isUnit M hM hD)]
  congr 2
  unfold blockSchur
  abel

end Algebra

namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

/-- The exact real charge of the edges discarded by an induced restriction. -/
def restrictionLoss (g : DeficientGraph V d) (S : Set V) (v : S) : ℝ :=
  ((g.graph.degree v.val : ℝ) - ((g.graph.induce S).degree v : ℝ)) / ((d : ℝ) - 1)

def restrictionLossDiagonal (g : DeficientGraph V d) (S : Set V) : Matrix S S ℂ :=
  Matrix.diagonal (fun v => (g.restrictionLoss S v : ℂ))

omit [DecidableEq V] in
theorem restrict_boundaryCoefficient (g : DeficientGraph V d) (S : Set V) (v : S) :
    (g.restrict S).boundaryCoefficient v = g.boundaryCoefficient v.val + g.restrictionLoss S v := by
  change ((d : ℝ) - (g.deficit v.val : ℝ) - ((g.graph.induce S).degree v : ℝ)) / _ =
    ((d : ℝ) - (g.deficit v.val : ℝ) - (g.graph.degree v.val : ℝ)) / _ + _
  unfold restrictionLoss
  ring

theorem restrict_boundaryDiagonal (g : DeficientGraph V d) (S : Set V) :
    (g.restrict S).boundaryDiagonal = g.boundaryDiagonal.submatrix
      (Subtype.val : S → V) (Subtype.val : S → V) + g.restrictionLossDiagonal S := by
  ext i j
  simp only [boundaryDiagonal, restrictionLossDiagonal, Matrix.submatrix_apply,
    Matrix.add_apply, Matrix.diagonal_apply, g.restrict_boundaryCoefficient]
  by_cases h : i = j
  · subst j; simp
  · have hval : i.val ≠ j.val := fun hh => h (Subtype.ext hh)
    simp [h, hval]

theorem restrict_extensionMatrix (g : DeficientGraph V d) (S : Set V) (w z : ℂ) :
    (g.restrict S).extensionMatrix w z = (g.extensionMatrix w z).submatrix
      (Subtype.val : S → V) (Subtype.val : S → V) - w • g.restrictionLossDiagonal S := by
  change spectralMatrix (g.restrict S).H z - w • (g.restrict S).boundaryDiagonal = _
  rw [g.H_restrict S, g.restrict_boundaryDiagonal S,
    spectralMatrix_principal g.H z (Subtype.val : S → V) Subtype.val_injective]
  ext i j
  simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.add_apply,
    Pi.smul_apply, smul_eq_mul]
  change _ - w * (_ + _) = (_ - w * _) - w * _
  ring

/-- Actual source (B.13)--(B.14) localization identity, before estimating
the boundary self-energy. The outside inverse is the genuine deleted model. -/
theorem extensionGreen_localization_identity (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    (g.restrict S).extensionGreen q z - (g.extensionGreen q z).submatrix
      (Subtype.val : S → V) (Subtype.val : S → V) =
      (g.restrict S).extensionGreen q z *
        (q • g.restrictionLossDiagonal S -
          (g.extensionMatrix q z).submatrix (Subtype.val : S → V) (Subtype.val : (Sᶜ : Set V) → V) *
          (g.delete S).extensionGreen q z *
          (g.extensionMatrix q z).submatrix (Subtype.val : (Sᶜ : Set V) → V) (Subtype.val : S → V)) *
        (g.extensionGreen q z).submatrix (Subtype.val : S → V) (Subtype.val : S → V) := by
  let M := partitionMatrix S (g.extensionMatrix q z)
  have hM : IsUnit M := partitionMatrix_isUnit S _ (g.extensionMatrix_isUnit hd q z hz hq)
  have hD : IsUnit M.toBlocks₂₂ := by
    simpa only [M, partitionMatrix22, ← g.extensionMatrix_delete S q z] using
      (g.delete S).extensionMatrix_isUnit hd q z hz hq
  have hP : IsUnit (M.toBlocks₁₁ - q • g.restrictionLossDiagonal S) := by
    simpa only [M, partitionMatrix11, ← g.restrict_extensionMatrix S q z] using
      (g.restrict S).extensionMatrix_isUnit hd q z hz hq
  have h := block_localization_identity M (q • g.restrictionLossDiagonal S) hM hD hP
  simpa only [M, partitionMatrix_inverse, partitionMatrix11, partitionMatrix12,
    partitionMatrix21, partitionMatrix22, ← g.restrict_extensionMatrix S q z,
    ← g.extensionMatrix_delete S q z] using h

end DeficientGraph
end LocalLaw
