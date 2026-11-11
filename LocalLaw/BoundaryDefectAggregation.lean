import Mathlib

/-!
# Aggregate sparse bad-label defects

An actual entrywise estimate for every off-diagonal pair with at least one
good endpoint gives column sums and weighted row/cavity forcing. The number
of bad labels enters explicitly, rather than a desired column-sum premise.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance boundaryDefectAggregationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {I : Type*} [Fintype I]

theorem sparse_boundary_defect_column_sum (D : I → I → ℂ) (bad : Finset I)
    (B : ℕ) (δ γ : ℝ) (hB : bad.card ≤ B) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (hglobal : ∀ i j, ‖D i j‖ ≤ δ)
    (hgood : ∀ i j, i ≠ j → (i ∉ bad ∨ j ∉ bad) → ‖D i j‖ ≤ γ) (j : I) :
    ∑ i, ‖D i j‖ ≤ ((B : ℝ) + 1) * δ + (Fintype.card I : ℝ) * γ := by
  classical
  have hpoint (i : I) : ‖D i j‖ ≤ (if i ∈ bad then δ else 0) +
      (if i = j then δ else 0) + γ := by
    by_cases hi : i ∈ bad
    · simp only [if_pos hi]
      have hz : 0 ≤ (if i = j then δ else 0) := by split_ifs <;> positivity
      linarith [hglobal i j]
    · simp only [if_neg hi,zero_add]
      by_cases hij : i = j
      · rw [if_pos hij]
        exact (hglobal i j).trans (le_add_of_nonneg_right hγ)
      · rw [if_neg hij,zero_add]
        exact hgood i j hij (Or.inl hi)
  calc
    _ ≤ ∑ i, ((if i ∈ bad then δ else 0) + (if i = j then δ else 0) + γ) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = (bad.card : ℝ) * δ + δ + (Fintype.card I : ℝ) * γ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.mem_univ,
        Finset.sum_ite_eq', Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hB : (bad.card : ℝ) ≤ B) hδ]

theorem sparse_boundary_defect_weighted_offdiag (D : I → I → ℂ) (bad : Finset I)
    (A B : I → ℂ) (δ γ : ℝ) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (hglobal : ∀ i j, ‖D i j‖ ≤ δ)
    (hgood : ∀ i j, i ≠ j → (i ∉ bad ∨ j ∉ bad) → ‖D i j‖ ≤ γ) :
    ‖∑ i, ∑ j, if i = j then 0 else A i * D i j * B j‖ ≤
      δ * (∑ i ∈ bad, ‖A i‖) * (∑ j ∈ bad, ‖B j‖) +
        γ * (∑ i, ‖A i‖) * (∑ j, ‖B j‖) := by
  classical
  have hpoint (i j : I) : ‖if i = j then 0 else A i * D i j * B j‖ ≤
      δ * (if i ∈ bad then ‖A i‖ else 0) * (if j ∈ bad then ‖B j‖ else 0) +
        γ * ‖A i‖ * ‖B j‖ := by
    by_cases hij : i = j
    · simp only [hij,if_true,norm_zero]
      positivity
    · simp only [hij,if_false,norm_mul]
      by_cases hi : i ∈ bad
      · by_cases hj : j ∈ bad
        · simp only [hi,hj,if_true]
          have h := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hglobal i j) (norm_nonneg (A i))) (norm_nonneg (B j))
          nlinarith [mul_nonneg (mul_nonneg hγ (norm_nonneg (A i))) (norm_nonneg (B j))]
        · simp only [hi,hj,if_true,if_false,mul_zero,zero_add]
          have h := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hgood i j hij (Or.inr hj)) (norm_nonneg (A i))) (norm_nonneg (B j))
          nlinarith
      · simp only [hi,if_false,mul_zero,zero_mul,zero_add]
        have h := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hgood i j hij (Or.inl hi)) (norm_nonneg (A i))) (norm_nonneg (B j))
        nlinarith
  calc
    _ ≤ ∑ i, ‖∑ j, if i = j then 0 else A i * D i j * B j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖if i = j then 0 else A i * D i j * B j‖ :=
      Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, (δ * (if i ∈ bad then ‖A i‖ else 0) * (if j ∈ bad then ‖B j‖ else 0) +
      γ * ‖A i‖ * ‖B j‖) := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpoint i j))
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

end LocalLaw
