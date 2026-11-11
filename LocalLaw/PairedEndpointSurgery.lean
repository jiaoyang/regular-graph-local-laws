import LocalLaw.LocalSurgeryStability

/-!
# An isolated sampled pair gives a squared-error off-diagonal estimate

The new model's detached endpoint forces its comparison row to use only the
old pair. Old correlation isolation then controls every entry outside that
pair, and the two actual resolvent equations give the improved new error.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance pairedEndpointSurgeryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem isolated_old_pair_error_row (R P : Matrix I I ℂ) (s : Finset I) (δ φ : ℝ)
    (hδ : 0 ≤ δ) (hφ : 0 ≤ φ) (hcard : s.card ≤ 2)
    (hE : ∀ k l, ‖(R - P) k l‖ ≤ δ)
    (hPzero : ∀ k ∈ s, ∀ l ∉ s, P k l = 0)
    (hRsmall : ∀ k ∈ s, ∀ l ∉ s, ‖R k l‖ ≤ φ)
    (k : I) (hk : k ∈ s) :
    ∑ l, ‖(R - P) k l‖ ≤ 2 * δ + (Fintype.card I : ℝ) * φ := by
  have hpoint : ∀ l, ‖(R - P) k l‖ ≤ (if l ∈ s then δ else 0) + φ := by
    intro l
    by_cases hl : l ∈ s
    · simpa only [hl, if_true] using (hE k l).trans (le_add_of_nonneg_right hφ)
    · simp only [Matrix.sub_apply, hPzero k hk l hl, sub_zero, hl, if_false, zero_add]
      exact hRsmall k hk l hl
  calc
    _ ≤ ∑ l, ((if l ∈ s then δ else 0) + φ) := Finset.sum_le_sum (fun l _ => hpoint l)
    _ = (s.card : ℝ) * δ + (Fintype.card I : ℝ) * φ := by
      simp [Finset.sum_add_distrib, ← Finset.sum_filter, nsmul_eq_mul]
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hδ) _

/-- Every other target whose comparison column misses the isolated pair
has a quadratic, rather than first-order, endpoint surgery error. -/
theorem surgery_off_diagonal_of_isolated_pair (R T P Q W : Matrix I I ℂ)
    (hT : T + R * W * T = R) (hQ : Q + Q * W * P = P)
    (C w δ φ : ℝ) (hC : 0 ≤ C) (hw : 0 ≤ w) (hδ : 0 ≤ δ) (hφ : 0 ≤ φ)
    (hQrow : ∀ i, ∑ j, ‖Q i j‖ ≤ C) (hQcol : ∀ j, ∑ i, ‖Q i j‖ ≤ C)
    (hWrow : ∀ i, ∑ j, ‖W i j‖ ≤ w) (hWcol : ∀ j, ∑ i, ‖W i j‖ ≤ w)
    (hE : ∀ i j, ‖(R - P) i j‖ ≤ δ)
    (hsmall : (Fintype.card I : ℝ) * (1 + C * w) * w * δ ≤ 1 / 2)
    (i j : I) (s : Finset I) (hcard : s.card ≤ 2)
    (hAsupport : ∀ k, k ∉ s → (1 - Q * W) i k = 0)
    (hBmiss : ∀ l ∈ s, (1 - W * Q) l j = 0)
    (hPzero : ∀ k ∈ s, ∀ l ∉ s, P k l = 0)
    (hRsmall : ∀ k ∈ s, ∀ l ∉ s, ‖R k l‖ ≤ φ) :
    ‖(T - Q) i j‖ ≤ (1 + C * w) ^ 2 * φ +
      2 * (1 + C * w) ^ 3 * (2 * δ + (Fintype.card I : ℝ) * φ) * w * δ := by
  apply surgery_local_entry_stability R T P Q W hT hQ C w δ
    (2 * δ + (Fintype.card I : ℝ) * φ) φ hC hw hδ (by positivity) hφ
    hQrow hQcol hWrow hWcol hE hsmall i j
  · intro k hk
    have hks : k ∈ s := by by_contra h; exact hk (hAsupport k h)
    exact isolated_old_pair_error_row R P s δ φ hδ hφ hcard hE hPzero hRsmall k hks
  · intro k l hk hl
    have hks : k ∈ s := by by_contra h; exact hk (hAsupport k h)
    have hls : l ∉ s := fun h => hl (hBmiss l h)
    simp only [Matrix.sub_apply, hPzero k hks l hls, sub_zero]
    exact hRsmall k hks l hls

end LocalLaw
