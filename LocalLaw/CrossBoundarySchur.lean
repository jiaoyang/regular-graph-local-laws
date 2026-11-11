import LocalLaw.FilledBoundarySchur
import LocalLaw.PhysicalBoundarySchur

/-! # Exact cross-block Schur identities for actual physical and filled models -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance crossBoundarySchurDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Algebra
variable {I J V : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem inverse_block12 (M : Matrix (I⊕J) (I⊕J) ℂ) (hM : IsUnit M)
    (hD : IsUnit M.toBlocks₂₂) :
    M⁻¹.toBlocks₁₂= -(M⁻¹.toBlocks₁₁*M.toBlocks₁₂*M.toBlocks₂₂⁻¹) := by
  have hh := congrArg Matrix.toBlocks₁₂ (block_inverse_formula M hM hD)
  simp only [Matrix.toBlocks_fromBlocks₁₂] at hh
  rw [←inverse_block11 M hM hD] at hh
  exact hh

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem principal_inverse_cross (T : Set V) (M : Matrix V V ℂ) (hM : IsUnit M)
    (hD : IsUnit (M.submatrix (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:(Tᶜ:Set V)→V))) :
    M⁻¹.submatrix (Subtype.val:T→V) (Subtype.val:(Tᶜ:Set V)→V)=
      -(M⁻¹.submatrix (Subtype.val:T→V) (Subtype.val:T→V)*
        M.submatrix (Subtype.val:T→V) (Subtype.val:(Tᶜ:Set V)→V)*
        (M.submatrix (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:(Tᶜ:Set V)→V))⁻¹) := by
  have hh := inverse_block12 (partitionMatrix T M) (partitionMatrix_isUnit T M hM)
    (by simpa only [partitionMatrix22] using hD)
  simpa only [partitionMatrix_inverse,partitionMatrix11,partitionMatrix12,partitionMatrix22] using hh

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem green_principal_cross (T : Set V) (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0<z.im) :
    (green H z).submatrix (Subtype.val:T→V) (Subtype.val:(Tᶜ:Set V)→V)=
      -((green H z).submatrix (Subtype.val:T→V) (Subtype.val:T→V)*
        H.submatrix (Subtype.val:T→V) (Subtype.val:(Tᶜ:Set V)→V)*
        green (H.submatrix (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:(Tᶜ:Set V)→V)) z) := by
  have hD := spectralMatrix_isUnit (H.submatrix (Subtype.val:(Tᶜ:Set V)→V) Subtype.val)
    (hH.submatrix _) z hz
  rw [spectralMatrix_principal H z Subtype.val Subtype.val_injective] at hD
  have hh := principal_inverse_cross T (spectralMatrix H z) (spectralMatrix_isUnit H hH z hz) hD
  rw [spectralMatrix_cross12,←spectralMatrix_principal H z Subtype.val Subtype.val_injective] at hh
  exact hh

end Algebra

namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

theorem extensionGreen_principal_cross (g : DeficientGraph V d) (hd : 3≤d)
    (T : Set V) (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) :
    (g.extensionGreen q z).submatrix (Subtype.val:T→V) (Subtype.val:(Tᶜ:Set V)→V)=
      -((g.extensionGreen q z).submatrix (Subtype.val:T→V) (Subtype.val:T→V)*
        g.H.submatrix (Subtype.val:T→V) (Subtype.val:(Tᶜ:Set V)→V)*
        (g.delete T).extensionGreen q z) := by
  have hD := (g.delete T).extensionMatrix_isUnit hd q z hz hq
  rw [g.extensionMatrix_delete] at hD
  have hh := principal_inverse_cross T (g.extensionMatrix q z) (g.extensionMatrix_isUnit hd q z hz hq) hD
  rw [g.extensionMatrix_cross12,←g.extensionMatrix_delete] at hh
  exact hh

end DeficientGraph
end LocalLaw
