import LocalLaw.SourceGoodDiagonalParameters
import LocalLaw.SourceWeightedObservation

/-!
# Passing the actual observation sum to the good switched diagonals

Only good labels require a new physical diagonal approximation. Rejected
or exceptional labels contribute through the already bounded old centered
observation, so no physical estimate at those labels is inserted.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance weightedGoodDiagonalDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem observation_centered_bound_of_mean_bias {E : Type*} [Fintype E] [Nonempty E]
    (Z : E → ℂ) (target : ℂ) (b bias : ℝ)
    (hZ : ∀ e, ‖Z e‖ ≤ b) (hmean : ‖finiteComplexMean Z - target‖ ≤ bias) (e : E) :
    ‖Z e - target‖ ≤ 2 * b + bias := by
  have ht : ‖target‖ ≤ b + bias := by
    have hh := (norm_sub_le_norm_sub_add_norm_sub target (finiteComplexMean Z) 0).trans
      (add_le_add (by simpa only [norm_sub_rev] using hmean) (by simpa using finiteComplexMean_norm_bound Z b hZ))
    simpa only [sub_zero, add_comm] using hh
  exact ((norm_sub_le _ _).trans (add_le_add (hZ e) ht)).trans_eq (by ring)

theorem weighted_good_diagonal_transfer {I : Type*} [Fintype I]
    (good : Finset I) (w V Z : I → ℂ) (Y Q : ℂ) (δ B : ℝ)
    (_hδ : 0 ≤ δ) (_hB : 0 ≤ B)
    (hgood : ∀ i ∈ good, ‖V i - Y - Z i‖ ≤ δ)
    (hbad : ∀ i ∉ good, ‖Z i - (Q - Y)‖ ≤ B) :
    ‖∑ i ∈ good, w i * (V i - Q)‖ ≤
      ‖∑ i, w i * (Z i - (Q - Y))‖ +
        δ * (∑ i ∈ good, ‖w i‖) + B * (∑ i ∈ Finset.univ \ good, ‖w i‖) := by
  let A := fun i => w i * (Z i - (Q - Y))
  let E := fun i => w i * (V i - Y - Z i)
  have hsplit : (∑ i ∈ good, w i * (V i - Q)) =
      (∑ i, A i) - (∑ i ∈ Finset.univ \ good, A i) + ∑ i ∈ good, E i := by
    have hu : good ⊆ (Finset.univ : Finset I) := Finset.subset_univ _
    have hs : (∑ i ∈ Finset.univ \ good, A i) + (∑ i ∈ good, A i) = ∑ i, A i :=
      Finset.sum_sdiff hu
    have hg : (∑ i ∈ good, w i * (V i - Q)) = (∑ i ∈ good, A i) + ∑ i ∈ good, E i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [A, E]
      ring
    rw [hg]
    congr 1
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hs)
  have he : ‖∑ i ∈ good, E i‖ ≤ δ * ∑ i ∈ good, ‖w i‖ := by
    calc
      _ ≤ ∑ i ∈ good, ‖E i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ good, ‖w i‖ * δ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [show E i = w i * (V i - Y - Z i) from rfl, norm_mul]
        exact mul_le_mul_of_nonneg_left (hgood i hi) (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hb : ‖∑ i ∈ Finset.univ \ good, A i‖ ≤ B * ∑ i ∈ Finset.univ \ good, ‖w i‖ := by
    calc
      _ ≤ ∑ i ∈ Finset.univ \ good, ‖A i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.univ \ good, ‖w i‖ * B := by
        apply Finset.sum_le_sum
        intro i hi
        rw [show A i = w i * (Z i - (Q - Y)) from rfl, norm_mul]
        exact mul_le_mul_of_nonneg_left (hbad i (Finset.mem_sdiff.mp hi).2) (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  rw [hsplit]
  have hh := (norm_add_le ((∑ i, A i) - ∑ i ∈ Finset.univ \ good, A i)
    (∑ i ∈ good, E i)).trans (add_le_add
    ((norm_sub_le (∑ i, A i) (∑ i ∈ Finset.univ \ good, A i)).trans (add_le_add_left hb _)) he)
  exact hh.trans_eq (by dsimp only [A]; ring)

/-- A maximum weight converts the literal exceptional sum to its finite
cardinality. The physical approximation is still required only on good labels. -/
theorem weighted_good_diagonal_card_transfer {I : Type*} [Fintype I]
    (good : Finset I) (w V Z : I → ℂ) (Y Q : ℂ) (δ B W : ℝ)
    (hδ : 0 ≤ δ) (hB : 0 ≤ B) (_hW : 0 ≤ W)
    (hgood : ∀ i ∈ good, ‖V i - Y - Z i‖ ≤ δ)
    (hbad : ∀ i ∉ good, ‖Z i - (Q - Y)‖ ≤ B)
    (hweight : ∀ i ∉ good, ‖w i‖ ≤ W) :
    ‖∑ i ∈ good, w i * (V i - Q)‖ ≤
      ‖∑ i, w i * (Z i - (Q - Y))‖ + δ * (∑ i, ‖w i‖) +
        B * ((Finset.univ \ good).card : ℝ) * W := by
  have hh := weighted_good_diagonal_transfer good w V Z Y Q δ B hδ hB hgood hbad
  have hg : (∑ i ∈ good, ‖w i‖) ≤ ∑ i, ‖w i‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => norm_nonneg _)
  have hb : (∑ i ∈ Finset.univ \ good, ‖w i‖) ≤ ((Finset.univ \ good).card : ℝ) * W := by
    calc
      _ ≤ ∑ _i ∈ Finset.univ \ good, W := Finset.sum_le_sum (fun i hi => hweight i (Finset.mem_sdiff.mp hi).2)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  exact hh.trans ((add_le_add (add_le_add_left (mul_le_mul_of_nonneg_left hg hδ) _)
    (mul_le_mul_of_nonneg_left hb hB)).trans_eq (by ring))

end LocalLaw
