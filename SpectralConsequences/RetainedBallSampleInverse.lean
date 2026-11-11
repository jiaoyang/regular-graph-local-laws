import SpectralConsequences.NestedRetainedPrecision
import LocalLaw.SelectedFirstGreen
import LocalLaw.BlockSchurRows

/-! # The retained precision on a cavity ball and separated sampled vertices

The lower inverse is the physical retained-ball precision. Its upper Schur
complement is exactly the physical sampled block after deleting the ball.
The final row bound is independent of the number of retained vertices.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1400000
namespace SpectralConsequences
open LocalLaw
local instance retainedBallSampleInverseDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

def retainedBallSampleEmbedding (T : Set V) (e : I ↪ (Tᶜ : Set V)) : I ⊕ T ↪ V where
  toFun
    | .inl i => (e i).val
    | .inr t => t.val
  inj' := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (e.injective (Subtype.ext hij))
      | inr j =>
        change (e i).val = j.val at hij
        exact False.elim ((e i).property (hij.symm ▸ j.property))
    | inr i =>
      cases j with
      | inl j =>
        change i.val = (e j).val at hij
        exact False.elim ((e j).property (hij ▸ i.property))
      | inr j => exact congrArg Sum.inr (Subtype.ext hij)

theorem retained_ball_sample_inverse_rows (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (T : Set V) (e : I ↪ (Tᶜ : Set V)) (z : ℂ) (hz : 0 < z.im)
    (P C δ : ℝ) (hP : 0 ≤ P) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hTrows : ∀ i : T, ∑ j : T,
      ‖((green H z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ i j‖ ≤ P)
    (hBrows : ∀ i, ∑ j,
      ‖((green (H.submatrix (Subtype.val : (Tᶜ : Set V) → V)
          (Subtype.val : (Tᶜ : Set V) → V)) z).submatrix e e)⁻¹ i j‖ ≤ C)
    (hcrossL : ∀ i (t : T), ‖green H z (e i).val t.val‖ ≤ δ)
    (hcrossR : ∀ (t : T) i, ‖green H z t.val (e i).val‖ ≤ δ)
    (hsmallT : (Fintype.card T : ℝ)*P*δ ≤ 1)
    (hsmallI : (Fintype.card I : ℝ)*P*δ ≤ 1) :
    let f := retainedBallSampleEmbedding T e
    let U := (green H z).submatrix f f
    ∀ i, ∑ j, ‖U⁻¹ i j‖ ≤ P+2*C := by
  dsimp only
  let f := retainedBallSampleEmbedding T e
  let U := (green H z).submatrix f f
  let D := (green H z).submatrix (Subtype.val : T → V) (Subtype.val : T → V)
  let S := (green (H.submatrix (Subtype.val : (Tᶜ : Set V) → V)
    (Subtype.val : (Tᶜ : Set V) → V)) z).submatrix e e
  have hUi : IsUnit U := embedded_green_submatrix_isUnit H hH z hz f
  have hD : U.toBlocks₂₂ = D := rfl
  have hDi : IsUnit U.toBlocks₂₂ := hD ▸ (green_retained_principal_inverse T H hH z hz).1
  have hS : blockSchur U = S := by
    ext i j
    have hh := congrArg (fun A : Matrix (Tᶜ : Set V) (Tᶜ : Set V) ℂ => A (e i) (e j))
      (green_deleted_principal T H hH z hz)
    dsimp only at hh
    simp only [Matrix.sub_apply,Matrix.submatrix_apply,Matrix.mul_apply,Finset.sum_mul] at hh
    change _ = green (H.submatrix (Subtype.val : (Tᶜ : Set V) → V)
      (Subtype.val : (Tᶜ : Set V) → V)) z (e i) (e j)
    simpa only [blockSchur, Matrix.sub_apply, Matrix.mul_apply, Finset.sum_mul] using hh.symm
  have hLeft : ∀ i, ∑ t : T, ‖U.toBlocks₁₂ i t‖ ≤ (Fintype.card T : ℝ)*δ := by
    intro i
    exact (Finset.sum_le_sum (fun t _ => hcrossL i t)).trans_eq (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul])
  have hRight : ∀ t : T, ∑ i, ‖U.toBlocks₂₁ t i‖ ≤ (Fintype.card I : ℝ)*δ := by
    intro t
    exact (Finset.sum_le_sum (fun i _ => hcrossR t i)).trans_eq (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul])
  apply block_inverse_row_sum_bound U hUi hDi C P 1 hC hP (by norm_num) le_rfl
  · simpa only [hS] using hBrows
  · simpa only [hD] using hTrows
  · intro i
    have hh := rectangular_product_row_sum_bound U.toBlocks₁₂ U.toBlocks₂₂⁻¹
      ((Fintype.card T : ℝ)*δ) P hP hLeft (by simpa only [hD] using hTrows) i
    exact hh.trans (by nlinarith only [hsmallT])
  · intro t
    have hh := rectangular_product_row_sum_bound U.toBlocks₂₂⁻¹ U.toBlocks₂₁
      P ((Fintype.card I : ℝ)*δ) (by positivity) (by simpa only [hD] using hTrows) hRight t
    exact hh.trans (by nlinarith only [hsmallI])

end SpectralConsequences
