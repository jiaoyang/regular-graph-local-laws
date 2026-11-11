import LocalLaw.BlockSchur
import LocalLaw.BoundarySchurRows

/-! Finite block-inverse row sums from the genuine Schur formula. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance blockSchurRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Product
variable {I J K : Type} [Fintype J] [Fintype K]

theorem rectangular_product_row_sum_bound (A : Matrix I K ℂ) (B : Matrix K J ℂ)
    (r s : ℝ) (hs : 0≤s) (hA : ∀ i,∑ k,‖A i k‖≤r) (hB : ∀ k,∑ j,‖B k j‖≤s) (i:I) :
    ∑ j,‖(A*B) i j‖≤r*s := by
  calc
    _ ≤ ∑ k,‖A i k‖*(∑ j,‖B k j‖) := matrix_product_row_norm_sum A B i
    _ ≤ ∑ k,‖A i k‖*s := Finset.sum_le_sum (fun k _=>mul_le_mul_of_nonneg_left (hB k) (norm_nonneg _))
    _ = (∑ k,‖A i k‖)*s := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hA i) hs

end Product

section Block
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- A bounded restored core and matching leaf couplings have bounded full
inverse rows. The conclusion follows from the exact block inverse. -/
theorem block_inverse_row_sum_bound (M : Matrix (I⊕J) (I⊕J) ℂ)
    (hM : IsUnit M) (hD : IsUnit M.toBlocks₂₂) (C p a : ℝ)
    (hC : 0≤C) (hp : 0≤p) (ha : 0≤a) (haOne : a≤1)
    (hS : ∀ i,∑ k,‖(blockSchur M)⁻¹ i k‖≤C)
    (hDrows : ∀ j,∑ k,‖M.toBlocks₂₂⁻¹ j k‖≤p)
    (hL : ∀ i,∑ j,‖(M.toBlocks₁₂*M.toBlocks₂₂⁻¹) i j‖≤a)
    (hR : ∀ j,∑ i,‖(M.toBlocks₂₂⁻¹*M.toBlocks₂₁) j i‖≤a) :
    ∀ u,∑ v,‖M⁻¹ u v‖≤p+2*C := by
  let X:=(blockSchur M)⁻¹
  let D:=M.toBlocks₂₂⁻¹
  let L:=M.toBlocks₁₂*D
  let R:=D*M.toBlocks₂₁
  have hform : M⁻¹=Matrix.fromBlocks X (-(X*L)) (-(R*X)) (D+R*X*L) := by
    simpa only [X,D,L,R,Matrix.mul_assoc] using block_inverse_formula M hM hD
  have hXL : ∀ i,∑ j,‖(X*L) i j‖≤C*a := rectangular_product_row_sum_bound X L C a ha hS hL
  have hRX : ∀ j,∑ i,‖(R*X) j i‖≤a*C := rectangular_product_row_sum_bound R X a C hC hR hS
  have hRXL : ∀ j,∑ k,‖(R*X*L) j k‖≤a*C*a :=
    rectangular_product_row_sum_bound (R*X) L (a*C) a ha hRX hL
  have hbottom (j:J) : ∑ k,‖(D+R*X*L) j k‖≤p+a*C*a := by
    calc
      _ ≤ ∑ k,(‖D j k‖+‖(R*X*L) j k‖) := Finset.sum_le_sum (fun k _=>norm_add_le _ _)
      _ = _ := Finset.sum_add_distrib
      _ ≤ _ := add_le_add (hDrows j) (hRXL j)
  intro u
  rw [hform]
  cases u with
  | inl i =>
    simp only [Fintype.sum_sum_type,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.neg_apply,norm_neg]
    have hh:=add_le_add (hS i) (hXL i)
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left haOne hC,hp])
  | inr j =>
    simp only [Fintype.sum_sum_type,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.neg_apply,norm_neg]
    have hleft : a*C≤C := by nlinarith only [mul_le_mul_of_nonneg_right haOne hC]
    have hright : a*C*a≤C :=
      (mul_le_mul_of_nonneg_right hleft ha).trans (by nlinarith only [mul_le_mul_of_nonneg_left haOne hC])
    exact (add_le_add (hRX j) (hbottom j)).trans (by linarith)

end Block
end LocalLaw
