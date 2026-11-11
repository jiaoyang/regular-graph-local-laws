import LocalLaw.BlockSchur
import LocalLaw.MatrixEntryStability

/-!
# Quantitative stability under principal deletion

This proves the matrix algebra underlying Proposition 5.1. The graph-specific
cross-sum and reference-inverse row/column bounds are explicit inputs; the
inverse perturbation and deleted-resolvent error estimates are conclusions.
-/

open scoped BigOperators

namespace LocalLaw

section RectangularProducts

variable {A K B : Type*} [Fintype K]

theorem rectangular_product_row_bound (M : Matrix A K ℂ) (N : Matrix K B ℂ)
    (i : A) (j : B) (r c : ℝ) (hc : 0 ≤ c)
    (hrow : (∑ k, ‖M i k‖) ≤ r) (hentry : ∀ k, ‖N k j‖ ≤ c) :
    ‖(M * N) i j‖ ≤ r * c := by
  calc
    ‖(M * N) i j‖ ≤ ∑ k, ‖M i k‖ * ‖N k j‖ := by
      simpa only [Matrix.mul_apply, norm_mul] using norm_sum_le Finset.univ (fun k => M i k * N k j)
    _ ≤ ∑ k, ‖M i k‖ * c := Finset.sum_le_sum (fun k _ =>
      mul_le_mul_of_nonneg_left (hentry k) (norm_nonneg _))
    _ = (∑ k, ‖M i k‖) * c := (Finset.sum_mul ..).symm
    _ ≤ r * c := mul_le_mul_of_nonneg_right hrow hc

theorem rectangular_product_column_bound (M : Matrix A K ℂ) (N : Matrix K B ℂ)
    (i : A) (j : B) (c r : ℝ) (hc : 0 ≤ c)
    (hentry : ∀ k, ‖M i k‖ ≤ c) (hcol : (∑ k, ‖N k j‖) ≤ r) :
    ‖(M * N) i j‖ ≤ c * r := by
  calc
    ‖(M * N) i j‖ ≤ ∑ k, ‖M i k‖ * ‖N k j‖ := by
      simpa only [Matrix.mul_apply, norm_mul] using norm_sum_le Finset.univ (fun k => M i k * N k j)
    _ ≤ ∑ k, c * ‖N k j‖ := Finset.sum_le_sum (fun k _ =>
      mul_le_mul_of_nonneg_right (hentry k) (norm_nonneg _))
    _ = c * ∑ k, ‖N k j‖ := (Finset.mul_sum ..).symm
    _ ≤ c * r := mul_le_mul_of_nonneg_left hcol hc

end RectangularProducts

section InverseSums

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Inverse entry stability for two explicitly invertible matrices. -/
theorem inverse_entry_stability_pair (U P : Matrix I I ℂ)
    (hU : IsUnit U) (hP : IsUnit P) (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hrow : ∀ i, (∑ k, ‖P⁻¹ i k‖) ≤ C)
    (hcol : ∀ j, (∑ k, ‖P⁻¹ k j‖) ≤ C)
    (hentry : ∀ i j, ‖(U - P) i j‖ ≤ δ)
    (hsmall : (Fintype.card I : ℝ) * C * δ ≤ 1 / 2) :
    ∀ i j, ‖(U⁻¹ - P⁻¹) i j‖ ≤ 2 * C ^ 2 * δ := by
  have heq : P + (U - P) = U := by abel
  have hunit : IsUnit (P + (U - P)) := by rw [heq]; exact hU
  intro i j
  have h := inverse_entry_stability P (U - P) hP hunit C δ hC hδ hrow hcol hentry hsmall i j
  simpa only [heq] using h

/-- The perturbed inverse retains both row and column sum bounds, with an
explicit factor two; this is derived from Claim-5.7 entry stability. -/
theorem inverse_row_column_stability (U P : Matrix I I ℂ)
    (hU : IsUnit U) (hP : IsUnit P) (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hrow : ∀ i, (∑ k, ‖P⁻¹ i k‖) ≤ C)
    (hcol : ∀ j, (∑ k, ‖P⁻¹ k j‖) ≤ C)
    (hentry : ∀ i j, ‖(U - P) i j‖ ≤ δ)
    (hsmall : (Fintype.card I : ℝ) * C * δ ≤ 1 / 2) :
    (∀ i, (∑ k, ‖U⁻¹ i k‖) ≤ 2 * C) ∧
    (∀ j, (∑ k, ‖U⁻¹ k j‖) ≤ 2 * C) := by
  have hdiff := inverse_entry_stability_pair U P hU hP C δ hC hδ hrow hcol hentry hsmall
  have hpoint : ∀ i j, ‖U⁻¹ i j‖ ≤ ‖P⁻¹ i j‖ + 2 * C ^ 2 * δ := by
    intro i j
    have h := norm_sub_le_norm_sub_add_norm_sub (U⁻¹ i j) (P⁻¹ i j) 0
    calc
      ‖U⁻¹ i j‖ ≤ ‖U⁻¹ i j - P⁻¹ i j‖ + ‖P⁻¹ i j‖ := by simpa only [sub_zero] using h
      _ ≤ 2 * C ^ 2 * δ + ‖P⁻¹ i j‖ := add_le_add (hdiff i j) le_rfl
      _ = ‖P⁻¹ i j‖ + 2 * C ^ 2 * δ := add_comm _ _
  have hdim : (Fintype.card I : ℝ) * (2 * C ^ 2 * δ) ≤ C := by
    have h := mul_le_mul_of_nonneg_left hsmall (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC)
    nlinarith
  constructor
  · intro i
    calc
      (∑ k, ‖U⁻¹ i k‖) ≤ ∑ k, (‖P⁻¹ i k‖ + 2 * C ^ 2 * δ) :=
        Finset.sum_le_sum (fun k _ => hpoint i k)
      _ = (∑ k, ‖P⁻¹ i k‖) + (Fintype.card I : ℝ) * (2 * C ^ 2 * δ) := by
        simp [Finset.sum_add_distrib, nsmul_eq_mul]
      _ ≤ 2 * C := by linarith [hrow i]
  · intro j
    calc
      (∑ k, ‖U⁻¹ k j‖) ≤ ∑ k, (‖P⁻¹ k j‖ + 2 * C ^ 2 * δ) :=
        Finset.sum_le_sum (fun k _ => hpoint k j)
      _ = (∑ k, ‖P⁻¹ k j‖) + (Fintype.card I : ℝ) * (2 * C ^ 2 * δ) := by
        simp [Finset.sum_add_distrib, nsmul_eq_mul]
      _ ≤ 2 * C := by linarith [hcol j]

end InverseSums

section SchurComparison

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
/-- A quantitative comparison of the actual Schur deletion expressions.
Uniform full-entry control and finite cross-sum estimates imply the deleted
entry bound; its conclusion is not assumed in any hypothesis. -/
theorem schur_deletion_difference_bound (G P : Matrix (I ⊕ J) (I ⊕ J) ℂ)
    (hG11 : IsUnit G.toBlocks₁₁) (hP11 : IsUnit P.toBlocks₁₁)
    (C L δ : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hentry : ∀ i j, ‖(G - P) i j‖ ≤ δ)
    (hrow : ∀ i, (∑ k, ‖P.toBlocks₁₁⁻¹ i k‖) ≤ C)
    (hcol : ∀ j, (∑ k, ‖P.toBlocks₁₁⁻¹ k j‖) ≤ C)
    (hcrossrow : ∀ i, (∑ k, ‖P.toBlocks₂₁ i k‖) ≤ L)
    (hcrosscol : ∀ j, (∑ k, ‖G.toBlocks₁₂ k j‖) ≤ L)
    (hsmall : (Fintype.card I : ℝ) * C * δ ≤ 1 / 2) (i j : J) :
    ‖((G.toBlocks₂₂ - G.toBlocks₂₁ * G.toBlocks₁₁⁻¹ * G.toBlocks₁₂) -
      (P.toBlocks₂₂ - P.toBlocks₂₁ * P.toBlocks₁₁⁻¹ * P.toBlocks₁₂)) i j‖ ≤
        (1 + 3 * C * L + 2 * C ^ 2 * L ^ 2) * δ := by
  have hretained : ∀ k l, ‖(G.toBlocks₁₁ - P.toBlocks₁₁) k l‖ ≤ δ := by
    intro k l
    exact hentry (Sum.inl k) (Sum.inl l)
  have hinverse := inverse_entry_stability_pair G.toBlocks₁₁ P.toBlocks₁₁ hG11 hP11
    C δ hC hδ hrow hcol hretained hsmall
  have hsums := inverse_row_column_stability G.toBlocks₁₁ P.toBlocks₁₁ hG11 hP11
    C δ hC hδ hrow hcol hretained hsmall
  have hfirst : ‖((G.toBlocks₂₁ - P.toBlocks₂₁) * G.toBlocks₁₁⁻¹ * G.toBlocks₁₂) i j‖
      ≤ 2 * C * L * δ := by
    have hleft : ∀ l, ‖((G.toBlocks₂₁ - P.toBlocks₂₁) * G.toBlocks₁₁⁻¹) i l‖ ≤ δ * (2 * C) := by
      intro l
      exact rectangular_product_column_bound _ _ i l δ (2 * C) hδ
        (fun k => hentry (Sum.inr i) (Sum.inl k)) (hsums.2 l)
    have h := rectangular_product_column_bound _ G.toBlocks₁₂ i j (δ * (2 * C)) L
      (by positivity) hleft (hcrosscol j)
    convert h using 1
    ring
  have hsecond : ‖(P.toBlocks₂₁ * (G.toBlocks₁₁⁻¹ - P.toBlocks₁₁⁻¹) * G.toBlocks₁₂) i j‖
      ≤ 2 * C ^ 2 * L ^ 2 * δ := by
    have hleft : ∀ l, ‖(P.toBlocks₂₁ * (G.toBlocks₁₁⁻¹ - P.toBlocks₁₁⁻¹)) i l‖ ≤
        L * (2 * C ^ 2 * δ) := by
      intro l
      exact rectangular_product_row_bound _ _ i l L (2 * C ^ 2 * δ)
        (by positivity) (hcrossrow i) (fun k => hinverse k l)
    have h := rectangular_product_column_bound _ G.toBlocks₁₂ i j (L * (2 * C ^ 2 * δ)) L
      (by positivity) hleft (hcrosscol j)
    convert h using 1
    ring
  have hthird : ‖(P.toBlocks₂₁ * P.toBlocks₁₁⁻¹ * (G.toBlocks₁₂ - P.toBlocks₁₂)) i j‖
      ≤ C * L * δ := by
    rw [Matrix.mul_assoc]
    have hright : ∀ k, ‖(P.toBlocks₁₁⁻¹ * (G.toBlocks₁₂ - P.toBlocks₁₂)) k j‖ ≤ C * δ := by
      intro k
      exact rectangular_product_row_bound _ _ k j C δ hδ (hrow k)
        (fun l => hentry (Sum.inl l) (Sum.inr j))
    have h := rectangular_product_row_bound P.toBlocks₂₁ _ i j L (C * δ)
      (mul_nonneg hC hδ) (hcrossrow i) hright
    convert h using 1
    ring
  have hdecomp : (G.toBlocks₂₂ - G.toBlocks₂₁ * G.toBlocks₁₁⁻¹ * G.toBlocks₁₂) -
      (P.toBlocks₂₂ - P.toBlocks₂₁ * P.toBlocks₁₁⁻¹ * P.toBlocks₁₂) =
      (G.toBlocks₂₂ - P.toBlocks₂₂) -
      (G.toBlocks₂₁ - P.toBlocks₂₁) * G.toBlocks₁₁⁻¹ * G.toBlocks₁₂ -
      P.toBlocks₂₁ * (G.toBlocks₁₁⁻¹ - P.toBlocks₁₁⁻¹) * G.toBlocks₁₂ -
      P.toBlocks₂₁ * P.toBlocks₁₁⁻¹ * (G.toBlocks₁₂ - P.toBlocks₁₂) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [hdecomp]
  simp only [Matrix.sub_apply]
  have hzero : ‖(G.toBlocks₂₂ - P.toBlocks₂₂) i j‖ ≤ δ := hentry (Sum.inr i) (Sum.inr j)
  calc
    _ ≤ ‖G.toBlocks₂₂ i j - P.toBlocks₂₂ i j‖ +
        ‖((G.toBlocks₂₁ - P.toBlocks₂₁) * G.toBlocks₁₁⁻¹ * G.toBlocks₁₂) i j‖ +
        ‖(P.toBlocks₂₁ * (G.toBlocks₁₁⁻¹ - P.toBlocks₁₁⁻¹) * G.toBlocks₁₂) i j‖ +
        ‖(P.toBlocks₂₁ * P.toBlocks₁₁⁻¹ * (G.toBlocks₁₂ - P.toBlocks₁₂)) i j‖ := by
      exact (norm_sub_le _ _).trans
        (add_le_add_right ((norm_sub_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)) _)
    _ ≤ δ + 2 * C * L * δ + 2 * C ^ 2 * L ^ 2 * δ + C * L * δ :=
      add_le_add (add_le_add (add_le_add hzero hfirst) hsecond) hthird
    _ = (1 + 3 * C * L + 2 * C ^ 2 * L ^ 2) * δ := by ring

/-- Proposition-5.1 algebra for two actual full inverses. All retained-block
unit hypotheses are derived from the original and deleted-block units. -/
theorem deleted_inverse_difference_bound (M N : Matrix (I ⊕ J) (I ⊕ J) ℂ)
    (hM : IsUnit M) (hN : IsUnit N) (hMD : IsUnit M.toBlocks₂₂) (hND : IsUnit N.toBlocks₂₂)
    (C L δ : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hentry : ∀ i j, ‖(M⁻¹ - N⁻¹) i j‖ ≤ δ)
    (hrow : ∀ i, (∑ k, ‖(N⁻¹).toBlocks₁₁⁻¹ i k‖) ≤ C)
    (hcol : ∀ j, (∑ k, ‖(N⁻¹).toBlocks₁₁⁻¹ k j‖) ≤ C)
    (hcrossrow : ∀ i, (∑ k, ‖(N⁻¹).toBlocks₂₁ i k‖) ≤ L)
    (hcrosscol : ∀ j, (∑ k, ‖(M⁻¹).toBlocks₁₂ k j‖) ≤ L)
    (hsmall : (Fintype.card I : ℝ) * C * δ ≤ 1 / 2) (i j : J) :
    ‖(M.toBlocks₂₂⁻¹ - N.toBlocks₂₂⁻¹) i j‖ ≤
      (1 + 3 * C * L + 2 * C ^ 2 * L ^ 2) * δ := by
  rw [deleted_block_inverse M hM hMD, deleted_block_inverse N hN hND]
  exact schur_deletion_difference_bound M⁻¹ N⁻¹ (inverse_block11_isUnit M hM hMD)
    (inverse_block11_isUnit N hN hND) C L δ hC hL hδ hentry hrow hcol hcrossrow hcrosscol hsmall i j

end SchurComparison

end LocalLaw
