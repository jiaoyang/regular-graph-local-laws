import LocalLaw.ScalarRecursion

/-!
# Spectral-edge gap estimates

The semicircle quadratic has two roots separated by a square root of
`z^2 - 4`. This module derives the exact gap scale from the real distance to
`{-2, 2}` and the positive imaginary part, rather than assuming a gap bound.
-/

namespace LocalLaw

/-- Distance of the real part to the two semicircle spectral edges. -/
noncomputable def edgeDistance (z : ℂ) : ℝ := min |z.re - 2| |z.re + 2|

/-- The regularized edge-distance parameter κ+η. -/
noncomputable def spectralScale (z : ℂ) : ℝ := edgeDistance z + z.im

theorem edgeDistance_nonneg (z : ℂ) : 0 ≤ edgeDistance z :=
  le_min (abs_nonneg _) (abs_nonneg _)

theorem spectralScale_pos {z : ℂ} (hz : 0 < z.im) : 0 < spectralScale z := by
  unfold spectralScale
  linarith [edgeDistance_nonneg z]

/-- The near-edge factor has at least half of the regularized edge scale. -/
theorem spectralScale_le_twice_edge_norm {z : ℂ} (hz : 0 < z.im) :
    spectralScale z ≤ 2 * ‖z - 2‖ ∧ spectralScale z ≤ 2 * ‖z + 2‖ := by
  have hκminus : edgeDistance z ≤ |z.re - 2| := min_le_left _ _
  have hκplus : edgeDistance z ≤ |z.re + 2| := min_le_right _ _
  have hrminus : |z.re - 2| ≤ ‖z - 2‖ := by
    simpa using Complex.abs_re_le_norm (z - 2)
  have hrplus : |z.re + 2| ≤ ‖z + 2‖ := by
    simpa using Complex.abs_re_le_norm (z + 2)
  have himinus : z.im ≤ ‖z - 2‖ := by
    simpa [abs_of_pos hz] using Complex.abs_im_le_norm (z - 2)
  have hiplus : z.im ≤ ‖z + 2‖ := by
    simpa [abs_of_pos hz] using Complex.abs_im_le_norm (z + 2)
  unfold spectralScale
  constructor <;> linarith

/-- At least one distance to the two endpoints is at least two, since their
separation is four. -/
theorem two_le_max_edge_norm (z : ℂ) : 2 ≤ max ‖z - 2‖ ‖z + 2‖ := by
  have hsum := norm_sub_le (z + 2) (z - 2)
  have hid : (z + 2) - (z - 2) = (4 : ℂ) := by ring
  rw [hid] at hsum
  norm_num at hsum
  have ha : ‖z - 2‖ ≤ max ‖z - 2‖ ‖z + 2‖ := le_max_left _ _
  have hb : ‖z + 2‖ ≤ max ‖z - 2‖ ‖z + 2‖ := le_max_right _ _
  linarith

/-- Squared root separation is bounded below by κ+η. -/
theorem spectralScale_le_edge_product {z : ℂ} (hz : 0 < z.im) :
    spectralScale z ≤ ‖z - 2‖ * ‖z + 2‖ := by
  obtain ⟨ha, hb⟩ := spectralScale_le_twice_edge_norm hz
  have hmax := two_le_max_edge_norm z
  by_cases hlarge : 2 ≤ ‖z - 2‖
  · have hp := mul_le_mul_of_nonneg_right hlarge (norm_nonneg (z + 2))
    nlinarith
  · have hlarge' : 2 ≤ ‖z + 2‖ := by
      by_contra h
      have hm : max ‖z - 2‖ ‖z + 2‖ < 2 := max_lt (lt_of_not_ge hlarge) (lt_of_not_ge h)
      linarith
    have hp := mul_le_mul_of_nonneg_left hlarge' (norm_nonneg (z - 2))
    nlinarith

/-- The endpoint selected by the real-part distance is at most κ+η away. -/
theorem min_edge_norm_le_spectralScale {z : ℂ} (hz : 0 < z.im) :
    min ‖z - 2‖ ‖z + 2‖ ≤ spectralScale z := by
  have hm : ‖z - 2‖ ≤ |z.re - 2| + z.im := by
    simpa [abs_of_pos hz] using Complex.norm_le_abs_re_add_abs_im (z - 2)
  have hp : ‖z + 2‖ ≤ |z.re + 2| + z.im := by
    simpa [abs_of_pos hz] using Complex.norm_le_abs_re_add_abs_im (z + 2)
  unfold spectralScale edgeDistance
  by_cases h : |z.re - 2| ≤ |z.re + 2|
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans hm
  · rw [min_eq_right (le_of_not_ge h)]
    exact (min_le_right _ _).trans hp

/-- The other endpoint is uniformly bounded on a bounded spectral domain. -/
theorem max_edge_norm_le {z : ℂ} {B : ℝ} (hB : ‖z‖ ≤ B) :
    max ‖z - 2‖ ‖z + 2‖ ≤ B + 2 := by
  apply max_le
  · have h := norm_sub_le z (2 : ℂ)
    norm_num at h
    linarith
  · have h := norm_add_le z (2 : ℂ)
    norm_num at h
    linarith

/-- Upper bound for squared root separation on the bounded spectral domain. -/
theorem edge_product_le_spectralScale {z : ℂ} (hz : 0 < z.im)
    {B : ℝ} (hB : ‖z‖ ≤ B) :
    ‖z - 2‖ * ‖z + 2‖ ≤ (B + 2) * spectralScale z := by
  have hnear := min_edge_norm_le_spectralScale hz
  have hfar := max_edge_norm_le hB
  have hs := (spectralScale_pos hz).le
  have hmin : 0 ≤ min ‖z - 2‖ ‖z + 2‖ := le_min (norm_nonneg _) (norm_nonneg _)
  have hprod := mul_le_mul hfar hnear hmin (by linarith [(norm_nonneg z).trans hB])
  have hid : max ‖z - 2‖ ‖z + 2‖ * min ‖z - 2‖ ‖z + 2‖ =
      ‖z - 2‖ * ‖z + 2‖ := by
    by_cases h : ‖z - 2‖ ≤ ‖z + 2‖
    · rw [max_eq_right h, min_eq_left h]
      ring
    · rw [max_eq_left (le_of_not_ge h), min_eq_right (le_of_not_ge h)]
  simpa only [hid] using hprod

/-- The root gap squared equals the product of distances to the two edges. -/
theorem cavity_root_gap_norm_sq {m z : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) :
    ‖m⁻¹ - m‖ ^ 2 = ‖z - 2‖ * ‖z + 2‖ := by
  have hid := congrArg norm (cavity_root_gap_sq hm)
  rw [norm_pow] at hid
  have hfactor : z ^ 2 - 4 = (z - 2) * (z + 2) := by ring
  rwa [hfactor, norm_mul] at hid

/-- Automatic two-sided gap bounds for the semicircle quadratic. These are
exactly the constants needed by the bounded-domain scalar stability theorem. -/
theorem cavity_root_gap_bounds {m z : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im)
    {B : ℝ} (hB : ‖z‖ ≤ B) :
    Real.sqrt (spectralScale z) ≤ ‖m⁻¹ - m‖ ∧
      ‖m⁻¹ - m‖ ≤ Real.sqrt (B + 2) * Real.sqrt (spectralScale z) := by
  have hgap := cavity_root_gap_norm_sq hm
  have hlow := spectralScale_le_edge_product hz
  have hupp := edge_product_le_spectralScale hz hB
  have hB0 : 0 ≤ B + 2 := by linarith [(norm_nonneg z).trans hB]
  constructor
  · have h := Real.sqrt_le_sqrt hlow
    rw [← hgap, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
    exact h
  · have h := Real.sqrt_le_sqrt hupp
    rw [← hgap, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
      Real.sqrt_mul hB0] at h
    exact h

end LocalLaw
