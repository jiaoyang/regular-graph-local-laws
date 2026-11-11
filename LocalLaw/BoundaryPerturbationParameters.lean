import LocalLaw.ClosureParameters

/-!
# Actual small boundary feedback on logarithmic balls

The positive-kernel perturbation theorem requires a product of the boundary
error and the graph diameter to be small.  At the actual source radius this
follows uniformly from the proved error bound; no new graph or probability
estimate is an input here.
-/

open Filter

namespace LocalLaw

/-- A square-root stability scale times a linearly logarithmic radius loses
only one inverse logarithm. -/
theorem radius_scalarScale_bound (L s ε A K : ℝ) (r a : ℕ)
    (hL : 1 ≤ L) (hs : 0 < s) (hε : 0 ≤ ε) (ha : 1 ≤ a)
    (hA : 0 ≤ A) (hK : 0 ≤ K)
    (herror : ε ≤ (L ^ (4 * a))⁻¹) (hr : (r : ℝ) ≤ A * L) :
    K * ((r : ℝ) + 1) * scalarScale s ε ≤ K * (A + 1) / L := by
  have hLp : 0 < L := by linarith
  have hp := pow_le_pow_right₀ hL (show 4 ≤ 4 * a by omega)
  have hi := inv_anti₀ (by positivity : 0 < L ^ 4) hp
  have hsq : ε ≤ (1 / L ^ 2) ^ 2 := by
    calc
      ε ≤ (L ^ 4)⁻¹ := herror.trans hi
      _ = (1 / L ^ 2) ^ 2 := by field_simp; ring
  have hroot : Real.sqrt ε ≤ 1 / L ^ 2 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩
  have hr' : (r : ℝ) + 1 ≤ (A + 1) * L := by nlinarith
  calc
    _ ≤ K * ((A + 1) * L) * (1 / L ^ 2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hr' hK
      · exact (scalarScale_le_sqrt hs hε).trans hroot
      · exact scalarScale_nonneg hε
      · positivity
    _ = K * (A + 1) / L := by field_simp; ring

/-- Every fixed positive feedback budget is eventually valid for the actual
source error and integer localization radius, uniformly in the spectral
parameter. -/
theorem eventually_source_radius_boundary_small (a b d : ℕ) (β K δ : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hβ : 0 < β)
    (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 < z.im →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      K * ((logarithmicRadius β d N : ℝ) + 1) *
        scalarScale (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z) ≤ δ := by
  let A := β / Real.log ((d - 1 : ℕ) : ℝ)
  have hk : (1 : ℝ) < ((d - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < d - 1 by omega)
  have hlogk := Real.log_pos hk
  have hA : 0 ≤ A := div_nonneg hβ.le hlogk.le
  filter_upwards [eventually_paperError_small a b d β ha hb hd hβ,
    eventually_log_ge_nat 1, eventually_log_ge_nat (K * (A + 1) / δ),
    eventually_ge_atTop 1] with N herror hlog hmargin hN
  intro z hz hscale
  have hr : (logarithmicRadius β d N : ℝ) ≤ A * Real.log (N : ℝ) := by
    have hcoord : 0 ≤ β * Real.log (N : ℝ) / Real.log ((d - 1 : ℕ) : ℝ) := by positivity
    have hf := Nat.floor_le hcoord
    change (logarithmicRadius β d N : ℝ) ≤ _ at hf
    convert hf using 1
    dsimp only [A]
    ring
  apply (radius_scalarScale_bound (Real.log (N : ℝ)) (spectralScale z)
    (graphPaperError a d N (logarithmicRadius β d N) z) A K _ a hlog
    (spectralScale_pos hz)
    (graphPaperError_nonnegative _ _ _ _ _ hN hz.le) (by omega) hA hK
    (herror z hz hscale) hr).trans
  apply (div_le_iff₀ (by linarith : 0 < Real.log (N : ℝ))).mpr
  have hh := (div_le_iff₀ hδ).mp hmargin
  linarith

/-- The precise half-sized kernel feedback hypothesis follows from an actual
Q prior, with diameter bound 2r+1 and any fixed model constants. -/
theorem eventually_source_kernel_feedback (a b d : ℕ) (β C1 C C₀ : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hβ : 0 < β)
    (hC1 : 0 ≤ C1) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ N : ℕ in atTop, ∀ z q : ℂ, 0 < z.im →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ‖q - semicircleRoot z‖ ≤ C1 *
        scalarScale (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z) →
      ‖q - semicircleRoot z‖ * C * C₀ * (2 * (logarithmicRadius β d N : ℝ) + 1) ≤ 1 / 2 := by
  filter_upwards [eventually_source_radius_boundary_small a b d β (2 * C1 * C * C₀)
    (1 / 2) ha hb hd hβ (by positivity) (by norm_num), eventually_ge_atTop 1] with N hsmall hN
  intro z q hz hscale hprior
  have hs := hsmall z hz hscale
  have hε : 0 ≤ scalarScale (spectralScale z)
      (graphPaperError a d N (logarithmicRadius β d N) z) :=
    scalarScale_nonneg (graphPaperError_nonnegative a d N (logarithmicRadius β d N) z hN hz.le)
  have hr : 0 ≤ (logarithmicRadius β d N : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hprior
    (show 0 ≤ C * C₀ * (2 * (logarithmicRadius β d N : ℝ) + 1) by positivity)
  calc
    _ ≤ C1 * scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) *
        (C * C₀ * (2 * (logarithmicRadius β d N : ℝ) + 1)) := by nlinarith [hmul]
    _ ≤ (2 * C1 * C * C₀) * ((logarithmicRadius β d N : ℝ) + 1) *
        scalarScale (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z) := by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC1 hC) hC₀) hε]
    _ ≤ 1 / 2 := hs

end LocalLaw
