import LocalLaw.PhysicalMinorSurgery
import LocalLaw.FiniteRankSurgery

/-!
# Genuine target-to-endpoint rows through supported inverse surgery

The augmented post model needs no reference-class premise. Its endpoint
block and the old target row control the new target row through the actual
inverse identity. Entry approximation transfers endpoint row sums directly.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance augmentedRowTransferDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

omit [Fintype V] [DecidableEq V] [DecidableEq I] in
theorem endpoint_row_sum_of_entry_approximation (U Q : Matrix I I ℂ) (C δ : ℝ)
    (_hC : 0 ≤ C) (_hδ : 0 ≤ δ)
    (hQ : ∀ i, ∑ j, ‖Q i j‖ ≤ C) (happrox : ∀ i j, ‖U i j - Q i j‖ ≤ δ) :
    ∀ i, ∑ j, ‖U i j‖ ≤ C + (Fintype.card I : ℝ) * δ := by
  intro i
  calc
    _ ≤ ∑ j, (‖Q i j‖ + δ) := by
      apply Finset.sum_le_sum
      intro j _
      have hh := norm_sub_le_norm_sub_add_norm_sub (U i j) (Q i j) 0
      simp only [sub_zero] at hh
      linarith [happrox i j]
    _ = (∑ j, ‖Q i j‖) + (Fintype.card I : ℝ) * δ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := add_le_add_right (hQ i) _

omit [DecidableEq I] in
theorem inverse_supported_endpoint_row_sum (A B : Matrix V V ℂ) (hA : IsUnit A) (hB : IsUnit B)
    (e : I ↪ V)
    (hsupport : ∀ x y, x ∉ Set.range e ∨ y ∉ Set.range e → (B - A) x y = 0)
    (a C w : ℝ) (ha : 0 ≤ a) (hC : 0 ≤ C) (hw : 0 ≤ w) (x : V)
    (hOld : ∑ i, ‖A⁻¹ x (e i)‖ ≤ a)
    (hNew : ∀ i, ∑ j, ‖B⁻¹ (e i) (e j)‖ ≤ C)
    (hW : ∀ i, ∑ j, ‖(B - A) (e i) (e j)‖ ≤ w) :
    (∑ i, ‖B⁻¹ x (e i)‖) ≤ a * (1 + w * C) := by
  cases isEmpty_or_nonempty I with
  | inl hI =>
    letI := hI
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    positivity
  | inr hI =>
    letI := hI
    let i0 : I := Classical.choice hI
    let R : Matrix I I ℂ := fun _ j => A⁻¹ x (e j)
    let U := B⁻¹.submatrix e e
    let W := (B - A).submatrix e e
    have hR : ∀ i, ∑ j, ‖R i j‖ ≤ a := fun _ => hOld
    have hW' : ∀ i, ∑ j, ‖W i j‖ ≤ w := hW
    have hU : ∀ i, ∑ j, ‖U i j‖ ≤ C := hNew
    have hRW := matrix_product_row_sum_bound R W a w hw hR hW'
    have hRWU := matrix_product_row_sum_bound (R * W) U (a * w) C hC hRW hU i0
    have hdiff : A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
      rw [Matrix.inv_sub_inv (show IsUnit A ↔ IsUnit B from ⟨fun _ => hB, fun _ => hA⟩)]
    have hrow (j : I) : B⁻¹ x (e j) = R i0 j - (R * W * U) i0 j := by
      have hh := congrArg (fun M : Matrix V V ℂ => M x (e j)) hdiff
      dsimp only at hh
      rw [Matrix.sub_apply, supported_middle_entry e _ _ _ hsupport] at hh
      have hprod : (R * W * U) i0 j =
          ∑ u, ∑ v, A⁻¹ x (e u) * ((B - A) (e u) (e v) * B⁻¹ (e v) (e j)) := by
        rw [Matrix.mul_assoc, Matrix.mul_apply]
        simp only [Matrix.mul_apply, R, W, U, Matrix.submatrix_apply, Finset.mul_sum]
      change B⁻¹ x (e j) = A⁻¹ x (e j) - (R * W * U) i0 j
      rw [hprod]
      linear_combination -hh
    calc
      _ = ∑ j, ‖R i0 j - (R * W * U) i0 j‖ := Finset.sum_congr rfl (fun j _ => congrArg norm (hrow j))
      _ ≤ ∑ j, (‖R i0 j‖ + ‖(R * W * U) i0 j‖) := Finset.sum_le_sum (fun _ _ => norm_sub_le _ _)
      _ = (∑ j, ‖R i0 j‖) + ∑ j, ‖(R * W * U) i0 j‖ := Finset.sum_add_distrib
      _ ≤ a + (a * w) * C := add_le_add (hR i0) hRWU
      _ = _ := by ring

end LocalLaw
