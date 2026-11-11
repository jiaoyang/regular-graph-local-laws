import LocalLaw.ScalarStability
import LocalLaw.ErrorParameters

/-!
# Monotone budgets and explicit vertical spectral chains

Downward motion decreases s=kappa+eta. When the uninflated error increases,
the actual threshold inflation increases too, including its favorable jump.
The scalar stability scale is monotone under precisely these changes.
-/

namespace LocalLaw

private theorem scalarScale_eq_sqrt_sub (s ε : ℝ) (hs : 0 < s) (hε : 0 ≤ ε) :
    scalarScale s ε = Real.sqrt (s + ε) - s / Real.sqrt (s + ε) := by
  have hpos : 0 < Real.sqrt (s + ε) := Real.sqrt_pos.mpr (by linarith)
  unfold scalarScale
  apply (div_eq_iff (ne_of_gt hpos)).mpr
  have hsq := Real.sq_sqrt (show 0 ≤ s + ε by linarith)
  field_simp


/-- Increasing epsilon improves its regularized square-root stability scale. -/
theorem scalarScale_mono_error (s ε δ : ℝ) (hs : 0 < s) (hε : 0 ≤ ε) (hεδ : ε ≤ δ) :
    scalarScale s ε ≤ scalarScale s δ := by
  have hδ : 0 ≤ δ := hε.trans hεδ
  have hroot : Real.sqrt (s + ε) ≤ Real.sqrt (s + δ) := Real.sqrt_le_sqrt (by linarith)
  have hsmall : 0 < Real.sqrt (s + ε) := Real.sqrt_pos.mpr (by linarith)
  have hdiv : s / Real.sqrt (s + δ) ≤ s / Real.sqrt (s + ε) :=
    div_le_div_of_nonneg_left hs.le hsmall hroot
  rw [scalarScale_eq_sqrt_sub s ε hs hε, scalarScale_eq_sqrt_sub s δ hs hδ]
  linarith

/-- Decreasing the edge-distance scale improves the stability budget. -/
theorem scalarScale_antitone_scale (s t ε : ℝ) (ht : 0 < t) (hts : t ≤ s) (hε : 0 ≤ ε) :
    scalarScale s ε ≤ scalarScale t ε := by
  have hroot : Real.sqrt (t + ε) ≤ Real.sqrt (s + ε) := Real.sqrt_le_sqrt (by linarith)
  have hsmall : 0 < Real.sqrt (t + ε) := Real.sqrt_pos.mpr (by linarith)
  exact div_le_div_of_nonneg_left hε hsmall hroot

theorem scalarScale_mono (s t ε δ : ℝ) (ht : 0 < t) (hts : t ≤ s)
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ) : scalarScale s ε ≤ scalarScale t δ :=
  (scalarScale_antitone_scale s t ε ht hts hε).trans
    (scalarScale_mono_error t ε δ ht hε hεδ)

/-- The full thresholded budgets are monotone in the favorable vertical
configuration, without a same-branch hypothesis. -/
theorem vertical_error_budgets (L e₀ e₁ s₀ s₁ : ℝ)
    (hL : 1 ≤ L) (he₀ : 0 ≤ e₀) (he : e₀ ≤ e₁)
    (hs₁ : 0 < s₁) (hs : s₁ ≤ s₀) :
    inflateError L e₀ s₀ ≤ inflateError L e₁ s₁ ∧
      scalarScale s₀ (inflateError L e₀ s₀) ≤
        scalarScale s₁ (inflateError L e₁ s₁) := by
  have herror := inflateError_mono hL he₀ he hs
  exact ⟨herror, scalarScale_mono s₀ s₁ _ _ hs₁ hs (inflateError_nonnegative he₀) herror⟩

/-- A capped equally spaced vertical chain. -/
def verticalHeight (top bottom h : ℝ) (k : ℕ) : ℝ :=
  max bottom (top - (k : ℝ) * h)

@[simp] theorem verticalHeight_zero (top bottom h : ℝ) (horder : bottom ≤ top) :
    verticalHeight top bottom h 0 = top := by simp [verticalHeight, max_eq_right horder]

theorem verticalHeight_lower (top bottom h : ℝ) (k : ℕ) :
    bottom ≤ verticalHeight top bottom h k := le_max_left _ _

theorem verticalHeight_step (top bottom h : ℝ) (k : ℕ) (hh : 0 ≤ h) :
    0 ≤ verticalHeight top bottom h k - verticalHeight top bottom h (k + 1) ∧
      verticalHeight top bottom h k - verticalHeight top bottom h (k + 1) ≤ h := by
  have hn : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by norm_cast
  unfold verticalHeight
  rw [hn]
  constructor
  · apply sub_nonneg.mpr
    apply max_le_max_left
    nlinarith
  · apply sub_le_iff_le_add.mpr
    apply max_le
    · exact (le_max_left bottom (top - ((k : ℝ) + 1) * h)).trans (by linarith)
    · have hmax := le_max_right bottom (top - ((k : ℝ) + 1) * h)
      nlinarith

theorem verticalHeight_last (top bottom h : ℝ) (K : ℕ)
    (hcover : top - bottom ≤ (K : ℝ) * h) : verticalHeight top bottom h K = bottom := by
  unfold verticalHeight
  apply max_eq_left
  linarith

end LocalLaw
