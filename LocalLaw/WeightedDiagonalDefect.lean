import LocalLaw.WeightedGoodDiagonal

/-! # Reassemble the full diagonal defect after good-label concentration -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance weightedDiagonalDefectDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem weighted_diagonal_defect_transfer {I : Type*} [Fintype I]
    (good : Finset I) (w D V : I → ℂ) (Y q : ℂ) (E A δ W : ℝ)
    (_hE : 0 ≤ E) (_hA : 0 ≤ A) (hδ : 0 ≤ δ) (_hW : 0 ≤ W)
    (hgood : ∀ i ∈ good, D i = V i - Y)
    (hforce : ‖∑ i ∈ good, w i * (V i - q)‖ ≤ E)
    (hl1 : ∑ i, ‖w i‖ ≤ A) (hglobal : ∀ i, ‖D i‖ ≤ δ)
    (hmax : ∀ i ∉ good, ‖w i‖ ≤ W) :
    ‖∑ i, w i * D i‖ ≤ E + ‖q - Y‖ * A + δ * ((Finset.univ \ good).card : ℝ) * W := by
  let bad := Finset.univ \ good
  have hpartition : (∑ i ∈ bad, w i * D i) + (∑ i ∈ good, w i * D i) = ∑ i, w i * D i :=
    Finset.sum_sdiff (Finset.subset_univ good)
  have hsplit : (∑ i ∈ good, w i * D i) =
      (∑ i ∈ good, w i * (V i - q)) + (q - Y) * (∑ i ∈ good, w i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hgood i hi]
    ring
  have hsumGood : ‖∑ i ∈ good, w i‖ ≤ A := by
    apply (norm_sum_le _ _).trans
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ good)
      (fun _ _ _ => norm_nonneg _)).trans hl1
  have hgoodNorm : ‖∑ i ∈ good, w i * D i‖ ≤ E + ‖q - Y‖ * A := by
    rw [hsplit]
    apply (norm_add_le _ _).trans
    exact add_le_add hforce (by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hsumGood (norm_nonneg _))
  have hbadSum : (∑ i ∈ bad, ‖w i‖) ≤ (bad.card : ℝ) * W := by
    calc
      _ ≤ ∑ _i ∈ bad, W := Finset.sum_le_sum (fun i hi => hmax i (Finset.mem_sdiff.mp hi).2)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hbadNorm : ‖∑ i ∈ bad, w i * D i‖ ≤ δ * (bad.card : ℝ) * W := by
    calc
      _ ≤ ∑ i ∈ bad, ‖w i * D i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ bad, ‖w i‖ * δ := Finset.sum_le_sum (fun i _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hglobal i) (norm_nonneg _))
      _ = δ * (∑ i ∈ bad, ‖w i‖) := by rw [← Finset.sum_mul]; ring
      _ ≤ δ * ((bad.card : ℝ) * W) := mul_le_mul_of_nonneg_left hbadSum hδ
      _ = _ := by ring
  rw [← hpartition]
  exact ((norm_add_le _ _).trans (add_le_add hbadNorm hgoodNorm)).trans_eq (by dsimp only [bad]; ring)

end LocalLaw
