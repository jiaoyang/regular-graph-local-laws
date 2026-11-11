import LocalLaw.PrincipalDeletionWard

/-!
# Principal-deletion Ward bounds restricted to safe vertices

Use the actual deleted inverse on A x A, and the original inverse elsewhere.
Its pointwise change is either the actual principal Schur correction or zero.
Thus every weighted Ward bound remains valid, while diagonal/pivot estimates
for the deleted inverse are required only on the designated safe set A.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance guardedDeletionWardDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

def guardedDeletedGreen (H : Matrix V V ℂ) (T A : Set V) (z : ℂ) : Matrix V V ℂ :=
  fun i j => if i ∈ A ∧ j ∈ A then maskedDeletedGreen H T z i j else green H z i j

theorem guardedDeletedGreen_difference_bound (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (T A : Set V) (z : ℂ) (hz : 0 < z.im) (i j : V) :
    ‖green H z i j - guardedDeletedGreen H T A z i j‖ ≤ ‖principalSchurCorrection H T z i j‖ := by
  unfold guardedDeletedGreen
  split_ifs
  · exact maskedDeletedGreen_difference_bound H hH T z hz i j
  · simpa only [sub_self, norm_zero] using norm_nonneg (principalSchurCorrection H T z i j)

theorem weighted_guardedDeletedGreen_difference_ward (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (T A : Set V) (z : ℂ) (hz : 0 < z.im)
    (W : Matrix V V ℝ) (D I : ℝ) (hW : ∀ i j, 0 ≤ W i j) (hD : 0 ≤ D)
    (hrow : ∀ i, ∑ j, W i j = D) (hcol : ∀ j, ∑ i, W i j = D)
    (hI : ∀ u, (green H z u u).im ≤ I) :
    (∑ i, ∑ j, W i j * ‖green H z i j - guardedDeletedGreen H T A z i j‖) ≤
      (D * I / z.im) * (∑ u : T, ∑ v : T,
        ‖((green H z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ u v‖) := by
  apply le_trans _ (weighted_principalSchurCorrection_ward H hH T z hz W D I hW hD hrow hcol hI)
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
    mul_le_mul_of_nonneg_left (guardedDeletedGreen_difference_bound H hH T A z hz i j) (hW i j)))

theorem guardedDeletedGreen_of_safe (H : Matrix V V ℂ) (T A : Set V) (hA : A ⊆ Tᶜ)
    (z : ℂ) (i j : A) : guardedDeletedGreen H T A z i.val j.val =
      green (H.submatrix (Subtype.val : (Tᶜ : Set V) → V)
        (Subtype.val : (Tᶜ : Set V) → V)) z ⟨i.val, hA i.property⟩ ⟨j.val, hA j.property⟩ := by
  have hi : i.val ∉ T := hA i.property
  have hj : j.val ∉ T := hA j.property
  rw [guardedDeletedGreen, if_pos ⟨i.property, j.property⟩, maskedDeletedGreen, dif_pos hi, dif_pos hj]

/-- Local caps for the guarded inverse use no deleted pivot near T. -/
theorem guardedDeletedGreen_local_caps (G : SimpleGraph V) (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (T A : Set V) (hA : A ⊆ Tᶜ) (z : ℂ) (hz : 0 < z.im) (C L : ℝ)
    (hRd : ∀ i, ‖green H z i i‖ ≤ C)
    (hRe : ∀ i j, G.Adj i j → ‖green H z i j‖ ≤ C)
    (hRi : ∀ i, ‖(green H z i i)⁻¹‖ ≤ L)
    (hSd : ∀ i : A, ‖green (H.submatrix (Subtype.val : (Tᶜ : Set V) → V)
      (Subtype.val : (Tᶜ : Set V) → V)) z ⟨i.val, hA i.property⟩ ⟨i.val, hA i.property⟩‖ ≤ C)
    (hSe : ∀ i j : A, G.Adj i.val j.val →
      ‖green (H.submatrix (Subtype.val : (Tᶜ : Set V) → V)
        (Subtype.val : (Tᶜ : Set V) → V)) z ⟨i.val, hA i.property⟩ ⟨j.val, hA j.property⟩‖ ≤ C)
    (hSi : ∀ i : A, ‖(green (H.submatrix (Subtype.val : (Tᶜ : Set V) → V)
      (Subtype.val : (Tᶜ : Set V) → V)) z ⟨i.val, hA i.property⟩ ⟨i.val, hA i.property⟩)⁻¹‖ ≤ L) :
    (∀ i, ‖guardedDeletedGreen H T A z i i‖ ≤ C) ∧
      (∀ i j, G.Adj i j → ‖guardedDeletedGreen H T A z i j‖ ≤ C) ∧
      (∀ i, guardedDeletedGreen H T A z i i ≠ 0) ∧
      (∀ i, ‖(guardedDeletedGreen H T A z i i)⁻¹‖ ≤ L) := by
  constructor
  · intro i
    by_cases hi : i ∈ A
    · simpa only [guardedDeletedGreen_of_safe H T A hA z ⟨i, hi⟩ ⟨i, hi⟩] using hSd ⟨i, hi⟩
    · simpa only [guardedDeletedGreen, hi, false_and, if_false] using hRd i
  constructor
  · intro i j hij
    by_cases hi : i ∈ A
    · by_cases hj : j ∈ A
      · simpa only [guardedDeletedGreen_of_safe H T A hA z ⟨i, hi⟩ ⟨j, hj⟩] using hSe ⟨i, hi⟩ ⟨j, hj⟩ hij
      · simpa only [guardedDeletedGreen, hj, and_false, if_false] using hRe i j hij
    · simpa only [guardedDeletedGreen, hi, false_and, if_false] using hRe i j hij
  constructor
  · intro i
    by_cases hi : i ∈ A
    · rw [guardedDeletedGreen_of_safe H T A hA z ⟨i, hi⟩ ⟨i, hi⟩]
      exact green_diagonal_ne_zero _ (hH.submatrix _) z hz _
    · simpa only [guardedDeletedGreen, hi, false_and, if_false] using green_diagonal_ne_zero H hH z hz i
  · intro i
    by_cases hi : i ∈ A
    · simpa only [guardedDeletedGreen_of_safe H T A hA z ⟨i, hi⟩ ⟨i, hi⟩] using hSi ⟨i, hi⟩
    · simpa only [guardedDeletedGreen, hi, false_and, if_false] using hRi i

end LocalLaw
