import LocalLaw.ScalarStability

/-!
# Error-budget comparison within one spectral branch

Relative perturbations of s and epsilon yield an explicit margin between a
strict budget at the representative and the weak budget at the target. The
hypotheses concern values inside one branch; no continuity across the jump
in the paper's error definition is asserted.
-/

namespace LocalLaw

/-- Multiplicative comparison of the square-root stability scale. -/
theorem scalarScale_relative_bound (s t ε δ a b : ℝ)
    (hs : 0 < s) (hε : 0 < ε) (htδ : 0 < t + δ)
    (ha : 0 ≤ a) (hb : 0 < b) (hδ : δ ≤ a * ε)
    (hden : b ^ 2 * (s + ε) ≤ t + δ) :
    scalarScale t δ ≤ (a / b) * scalarScale s ε := by
  have hroot : 0 < Real.sqrt (s + ε) := Real.sqrt_pos.mpr (by linarith)
  have hroot' : 0 < Real.sqrt (t + δ) := Real.sqrt_pos.mpr htδ
  have hcomp : b * Real.sqrt (s + ε) ≤ Real.sqrt (t + δ) := by
    have hsq : (b * Real.sqrt (s + ε)) ^ 2 ≤ (Real.sqrt (t + δ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ s + ε), Real.sq_sqrt htδ.le]
      exact hden
    nlinarith [Real.sqrt_nonneg (s + ε), Real.sqrt_nonneg (t + δ)]
  unfold scalarScale
  apply (div_le_iff₀ hroot').mpr
  have hnonneg : 0 ≤ (a / b) * (ε / Real.sqrt (s + ε)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcomp hnonneg
  have heq : (a / b * (ε / Real.sqrt (s + ε))) *
      (b * Real.sqrt (s + ε)) = a * ε := by
    field_simp
  rw [heq] at hmul
  exact hδ.trans hmul

/-- Relative changes of at most one eighth leave a quarter of the target
scale for transporting the analytic defect. -/
theorem scalarScale_budget_margin (s t ε δ : ℝ)
    (hs : 0 < s) (hε : 0 < ε)
    (hsvar : |t - s| ≤ s / 8) (hεvar : |δ - ε| ≤ ε / 8) :
    scalarScale t δ / 2 ≤ 3 / 4 * scalarScale s ε := by
  have ht : 0 < t := by have := (abs_le.mp hsvar).1; linarith
  have hδ : 0 < δ := by have := (abs_le.mp hεvar).1; linarith
  have heps : δ ≤ (9 / 8 : ℝ) * ε := by
    have := (abs_le.mp hεvar).2
    linarith
  have hden : (3 / 4 : ℝ) ^ 2 * (s + ε) ≤ t + δ := by
    have hslow := (abs_le.mp hsvar).1
    have helow := (abs_le.mp hεvar).1
    nlinarith
  have hb := scalarScale_relative_bound s t ε δ (9 / 8) (3 / 4)
    hs hε (by linarith) (by norm_num) (by norm_num) heps hden
  norm_num at hb
  linarith

/-- The corresponding unregularized epsilon budget has at least the same
quarter-margin under the same relative comparison. -/
theorem epsilon_budget_margin (ε δ : ℝ) (hε : 0 ≤ ε)
    (hvar : |δ - ε| ≤ ε / 8) : δ / 2 ≤ 3 / 4 * ε := by
  have := (abs_le.mp hvar).2
  linarith

/-- A complete transport-budget comparison, with both strict-budget margins
and analytic variation on the left-hand side. -/
theorem local_budget_comparison (s t ε δ Kc Ke h : ℝ)
    (hs : 0 < s) (hε : 0 < ε)
    (hsvar : |t - s| ≤ s / 8) (hεvar : |δ - ε| ≤ ε / 8)
    (hc : Kc * h ≤ scalarScale s ε / 4) (he : Ke * h ≤ ε / 4) :
    scalarScale t δ / 2 + Kc * h ≤ scalarScale s ε ∧ δ / 2 + Ke * h ≤ ε := by
  constructor
  · have := scalarScale_budget_margin s t ε δ hs hε hsvar hεvar
    linarith
  · have := epsilon_budget_margin ε δ hε.le hεvar
    linarith

end LocalLaw
