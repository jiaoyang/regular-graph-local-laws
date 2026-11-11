import LocalLaw.DeletionStability

/-!
# Target-specific Schur deletion stability

Only the retained block and the target row, column and entry are compared.
This matches the actual localization available from a neighborhood of the
removed set together with the two target vertices.
-/

open scoped BigOperators
namespace LocalLaw
variable {I J : Type*} [Fintype I] [DecidableEq I]

/-- The final deleted target entry depends only on four approximation blocks,
not on entries between arbitrary other outside vertices. -/
theorem target_schur_deletion_difference_bound (G P : Matrix (I ⊕ J) (I ⊕ J) ℂ)
    (hG11 : IsUnit G.toBlocks₁₁) (hP11 : IsUnit P.toBlocks₁₁)
    (C L δ : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hδ : 0 ≤ δ) (i j : J)
    (hTT : ∀ k l, ‖(G.toBlocks₁₁ - P.toBlocks₁₁) k l‖ ≤ δ)
    (hrowError : ∀ k, ‖G.toBlocks₂₁ i k - P.toBlocks₂₁ i k‖ ≤ δ)
    (hcolumnError : ∀ l, ‖G.toBlocks₁₂ l j - P.toBlocks₁₂ l j‖ ≤ δ)
    (htarget : ‖G.toBlocks₂₂ i j - P.toBlocks₂₂ i j‖ ≤ δ)
    (hrow : ∀ k, (∑ l, ‖P.toBlocks₁₁⁻¹ k l‖) ≤ C)
    (hcol : ∀ l, (∑ k, ‖P.toBlocks₁₁⁻¹ k l‖) ≤ C)
    (hcrossrow : (∑ k, ‖P.toBlocks₂₁ i k‖) ≤ L)
    (hcrosscol : (∑ k, ‖G.toBlocks₁₂ k j‖) ≤ L)
    (hsmall : (Fintype.card I : ℝ) * C * δ ≤ 1 / 2) :
    ‖((G.toBlocks₂₂ - G.toBlocks₂₁ * G.toBlocks₁₁⁻¹ * G.toBlocks₁₂) -
      (P.toBlocks₂₂ - P.toBlocks₂₁ * P.toBlocks₁₁⁻¹ * P.toBlocks₁₂)) i j‖ ≤
        (1 + 3 * C * L + 2 * C ^ 2 * L ^ 2) * δ := by
  have hretained : ∀ k l, ‖(G.toBlocks₁₁ - P.toBlocks₁₁) k l‖ ≤ δ := by
    intro k l
    exact hTT k l
  have hinverse := inverse_entry_stability_pair G.toBlocks₁₁ P.toBlocks₁₁ hG11 hP11
    C δ hC hδ hrow hcol hretained hsmall
  have hsums := inverse_row_column_stability G.toBlocks₁₁ P.toBlocks₁₁ hG11 hP11
    C δ hC hδ hrow hcol hretained hsmall
  have hfirst : ‖((G.toBlocks₂₁ - P.toBlocks₂₁) * G.toBlocks₁₁⁻¹ * G.toBlocks₁₂) i j‖
      ≤ 2 * C * L * δ := by
    have hleft : ∀ l, ‖((G.toBlocks₂₁ - P.toBlocks₂₁) * G.toBlocks₁₁⁻¹) i l‖ ≤ δ * (2 * C) := by
      intro l
      exact rectangular_product_column_bound _ _ i l δ (2 * C) hδ
        (fun k => hrowError k) (hsums.2 l)
    have h := rectangular_product_column_bound _ G.toBlocks₁₂ i j (δ * (2 * C)) L
      (by positivity) hleft hcrosscol
    convert h using 1
    ring
  have hsecond : ‖(P.toBlocks₂₁ * (G.toBlocks₁₁⁻¹ - P.toBlocks₁₁⁻¹) * G.toBlocks₁₂) i j‖
      ≤ 2 * C ^ 2 * L ^ 2 * δ := by
    have hleft : ∀ l, ‖(P.toBlocks₂₁ * (G.toBlocks₁₁⁻¹ - P.toBlocks₁₁⁻¹)) i l‖ ≤
        L * (2 * C ^ 2 * δ) := by
      intro l
      exact rectangular_product_row_bound _ _ i l L (2 * C ^ 2 * δ)
        (by positivity) hcrossrow (fun k => hinverse k l)
    have h := rectangular_product_column_bound _ G.toBlocks₁₂ i j (L * (2 * C ^ 2 * δ)) L
      (by positivity) hleft hcrosscol
    convert h using 1
    ring
  have hthird : ‖(P.toBlocks₂₁ * P.toBlocks₁₁⁻¹ * (G.toBlocks₁₂ - P.toBlocks₁₂)) i j‖
      ≤ C * L * δ := by
    rw [Matrix.mul_assoc]
    have hright : ∀ k, ‖(P.toBlocks₁₁⁻¹ * (G.toBlocks₁₂ - P.toBlocks₁₂)) k j‖ ≤ C * δ := by
      intro k
      exact rectangular_product_row_bound _ _ k j C δ hδ (hrow k)
        (fun l => hcolumnError l)
    have h := rectangular_product_row_bound P.toBlocks₂₁ _ i j L (C * δ)
      (mul_nonneg hC hδ) hcrossrow hright
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
  have hzero : ‖(G.toBlocks₂₂ - P.toBlocks₂₂) i j‖ ≤ δ := htarget
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

end LocalLaw
