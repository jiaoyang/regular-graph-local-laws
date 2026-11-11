import LocalLaw.GraphTheorem42
import LocalLaw.FiniteLocalization

/-!
# The actual paper error pays for localization tails

The physical transfer has squared norm at most 1/(d-1). Its two-sided tail
is therefore bounded by the literal localization term in the paper base
error, and inflation only increases that error when log(N)>=1.
-/

noncomputable section
namespace LocalLaw

theorem physical_transfer_two_sided_tail (d : ℕ) (hd : 3 ≤ d) (z : ℂ) (r : ℕ) :
    physicalTransfer d z ^ (2 * r) ≤ ((((d - 1 : ℕ) : ℝ) ^ r)⁻¹) := by
  have hsq := cavity_transfer_norm_sq_bound d hd (semicircleRoot z) (semicircleRoot_norm_le_one z)
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [pow_mul]
  apply (pow_le_pow_left₀ (sq_nonneg _) hsq r).trans_eq
  rw [← inv_pow, hcast]

theorem baseError_localization_lower (L : ℝ) (a d N r : ℕ) (η immd : ℝ)
    (hL : 1 ≤ L) (hη : 0 ≤ η) :
    ((((d - 1 : ℕ) : ℝ) ^ r)⁻¹) ≤ baseError L a d N r η immd := by
  have hterms := baseErrorTerms_nonnegative d N r η immd hη
  have hLpow : 1 ≤ L ^ (8 * a) := one_le_pow₀ hL
  have hloc : ((((d - 1 : ℕ) : ℝ) ^ r)⁻¹) ≤ baseErrorTerms d N r η immd := by
    unfold baseErrorTerms
    have hfrac : 0 ≤ (((N : ℝ) * η) ^ (2 / 3 : ℝ))⁻¹ := by positivity
    linarith [Real.sqrt_nonneg (immd / ((N : ℝ) * η))]
  have hmul := mul_le_mul_of_nonneg_right hLpow hterms
  exact hloc.trans (by simpa only [one_mul, baseError] using hmul)

/-- No tail-budget premise is needed at the actual source error. -/
theorem graphPaperError_localization_tail (a d N r : ℕ) (hd : 3 ≤ d) (z : ℂ)
    (hlog : 1 ≤ Real.log (N : ℝ)) (hz : 0 ≤ z.im) :
    physicalTransfer d z ^ (2 * r) ≤ graphPaperError a d N r z := by
  apply (physical_transfer_two_sided_tail d hd z r).trans
  apply (baseError_localization_lower (Real.log (N : ℝ)) a d N r z.im
    (graphKestenMcKayReference d z).im hlog hz).trans
  exact (inflateError_bounds hlog (baseError_nonnegative _ _ _ _ _ _ _ (by linarith) hz)).1

end LocalLaw
