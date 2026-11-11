import LocalLaw.DeletionStability

/-!
# Entrywise inverse stability between correlation blocks

A block-supported reference inverse and small entrywise perturbation give
both ordinary and cross-block inverse bounds. The cross-block bound keeps
the small off-block scale, rather than losing the entire perturbation scale.
This is the finite inverse algebra needed in source (5.58).
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sparseBlockInverseDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {I K : Type*} [Fintype I] [DecidableEq I]

theorem inverse_cross_block_stability (U P : Matrix I I ℂ)
    (hU : IsUnit U) (hP : IsUnit P) (label : I → K) (C δ φ : ℝ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hφ : 0 ≤ φ)
    (hrow : ∀ i, ∑ k, ‖P⁻¹ i k‖ ≤ C)
    (hcol : ∀ j, ∑ k, ‖P⁻¹ k j‖ ≤ C)
    (hblock : ∀ i j, label i ≠ label j → P⁻¹ i j = 0)
    (hentry : ∀ i j, ‖(U - P) i j‖ ≤ δ)
    (hoff : ∀ i j, label i ≠ label j → ‖(U - P) i j‖ ≤ φ)
    (hsmall : (Fintype.card I : ℝ) * C * δ ≤ 1 / 2)
    (i j : I) (hij : label i ≠ label j) : ‖U⁻¹ i j‖ ≤ 4 * C ^ 2 * φ := by
  let T := U⁻¹
  let E := U - P
  let Cross := {p : I × I // label p.1 ≠ label p.2}
  letI : Nonempty Cross := ⟨⟨(i, j), hij⟩⟩
  obtain ⟨p, hp⟩ := Finite.exists_max (fun x : Cross => ‖T x.val.1 x.val.2‖)
  let Γ := ‖T p.val.1 p.val.2‖
  have hΓ0 : 0 ≤ Γ := norm_nonneg _
  have hΓ : ∀ k l, label k ≠ label l → ‖T k l‖ ≤ Γ := fun k l h => hp ⟨(k, l), h⟩
  have hsums := inverse_row_column_stability U P hU hP C δ hC hδ hrow hcol hentry hsmall
  have hTcol : ∀ l, ∑ k, ‖T k l‖ ≤ 2 * C := hsums.2
  have hRP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP)
  have hUT : U * T = 1 := Matrix.mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det U).mp hU)
  have hidentity : T + P⁻¹ * E * T = P⁻¹ := by
    calc
      _ = (P⁻¹ * P) * T + P⁻¹ * E * T := by rw [hRP, Matrix.one_mul]
      _ = P⁻¹ * U * T := by dsimp only [E]; noncomm_ring
      _ = P⁻¹ := by rw [Matrix.mul_assoc, hUT, Matrix.mul_one]
  have hpoint : ∀ k l, label k ≠ label l →
      ‖T k l‖ ≤ C * ((Fintype.card I : ℝ) * δ * Γ + φ * (2 * C)) := by
    intro k l hkl
    have hET : ∀ v, label v = label k →
        ‖(E * T) v l‖ ≤ (Fintype.card I : ℝ) * δ * Γ + φ * (2 * C) := by
      intro v hv
      have hprod : ∀ u, ‖E v u‖ * ‖T u l‖ ≤ δ * Γ + φ * ‖T u l‖ := by
        intro u
        by_cases hu : label u = label k
        · have hul : label u ≠ label l := by rwa [hu]
          exact (mul_le_mul (hentry v u) (hΓ u l hul) (norm_nonneg _) hδ).trans
            (le_add_of_nonneg_right (mul_nonneg hφ (norm_nonneg _)))
        · have hvu : label v ≠ label u := by rw [hv]; exact Ne.symm hu
          exact (mul_le_mul_of_nonneg_right (hoff v u hvu) (norm_nonneg _)).trans
            (le_add_of_nonneg_left (mul_nonneg hδ hΓ0))
      calc
        _ ≤ ∑ u, ‖E v u‖ * ‖T u l‖ := matrix_mul_entry_norm_le E T v l
        _ ≤ ∑ u, (δ * Γ + φ * ‖T u l‖) := Finset.sum_le_sum (fun u _ => hprod u)
        _ = (Fintype.card I : ℝ) * δ * Γ + φ * (∑ u, ‖T u l‖) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, ← Finset.mul_sum]
          ring
        _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left (hTcol l) hφ) _
    have hentryid := congrArg (fun A : Matrix I I ℂ => A k l) hidentity
    have hzero := hblock k l hkl
    change T k l + (P⁻¹ * E * T) k l = P⁻¹ k l at hentryid
    rw [hzero] at hentryid
    have heq : T k l = -(P⁻¹ * E * T) k l := by linear_combination hentryid
    rw [heq, norm_neg, Matrix.mul_assoc]
    calc
      _ ≤ ∑ v, ‖P⁻¹ k v‖ * ‖(E * T) v l‖ := matrix_mul_entry_norm_le _ _ k l
      _ ≤ ∑ v, ‖P⁻¹ k v‖ * ((Fintype.card I : ℝ) * δ * Γ + φ * (2 * C)) := by
        apply Finset.sum_le_sum
        intro v _
        by_cases hv : label v = label k
        · exact mul_le_mul_of_nonneg_left (hET v hv) (norm_nonneg _)
        · rw [hblock k v (Ne.symm hv), norm_zero, zero_mul, zero_mul]
      _ = (∑ v, ‖P⁻¹ k v‖) * ((Fintype.card I : ℝ) * δ * Γ + φ * (2 * C)) :=
        (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow k) (by positivity)
  have hmax := hpoint p.val.1 p.val.2 p.property
  change Γ ≤ C * ((Fintype.card I : ℝ) * δ * Γ + φ * (2 * C)) at hmax
  have hscaled := mul_le_mul_of_nonneg_right hsmall hΓ0
  have habsorb : Γ ≤ 4 * C ^ 2 * φ := by nlinarith
  exact (hΓ i j hij).trans habsorb

end LocalLaw
