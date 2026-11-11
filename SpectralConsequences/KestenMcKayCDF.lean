import SpectralConsequences.KestenMcKayDensity
import SpectralConsequences.SquareRootCDF

/-! # The actual Kesten--McKay distribution as a compact square-root CDF

The CDF is an integral of the density. Its normalization and lower interval
mass are proved, rather than supplied as reference-law hypotheses.
-/

open Set MeasureTheory
open scoped Interval
noncomputable section
namespace SpectralConsequences
open LocalLaw

def kestenMcKayClip (x : ℝ) : ℝ := max (-2) (min 2 x)

theorem kestenMcKayClip_mem (x : ℝ) : kestenMcKayClip x ∈ Icc (-2 : ℝ) 2 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem kestenMcKayClip_eq {x : ℝ} (hx : x ∈ Icc (-2 : ℝ) 2) :
    kestenMcKayClip x = x := by
  simp only [kestenMcKayClip, min_eq_right hx.2, max_eq_right hx.1]

def kestenMcKayCDF (d : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (-2 : ℝ)..kestenMcKayClip x, kestenMcKayDensity d u

theorem kestenMcKayDensity_between_integrable (d : ℕ) (hd : 3 ≤ d)
    {x y : ℝ} (hx : -2 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2) :
    IntervalIntegrable (kestenMcKayDensity d) volume x y := by
  apply ContinuousOn.intervalIntegrable_of_Icc hxy
  exact (kestenMcKayDensity_continuousOn d hd).mono
    (fun u hu => ⟨hx.trans hu.1, hu.2.trans hy⟩)

theorem kestenMcKayCDF_continuous (d : ℕ) (hd : 3 ≤ d) :
    Continuous (kestenMcKayCDF d) := by
  have hp : ContinuousOn (fun b => ∫ u in (-2 : ℝ)..b, kestenMcKayDensity d u)
      (Icc (-2 : ℝ) 2) := by
    simpa only [uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 2)] using
      intervalIntegral.continuousOn_primitive_interval'
        (kestenMcKayDensity_intervalIntegrable d hd)
        (show (-2 : ℝ) ∈ uIcc (-2 : ℝ) 2 by simp)
  exact hp.comp_continuous
    (continuous_const.max (continuous_const.min continuous_id)) kestenMcKayClip_mem

theorem kestenMcKayCDF_monotone (d : ℕ) (hd : 3 ≤ d) :
    Monotone (kestenMcKayCDF d) := by
  intro x y hxy
  have hclip : kestenMcKayClip x ≤ kestenMcKayClip y :=
    max_le_max le_rfl (min_le_min le_rfl hxy)
  exact intervalIntegral.integral_mono_interval le_rfl (kestenMcKayClip_mem x).1 hclip
    (ae_of_all _ (fun u => kestenMcKayDensity_nonnegative d hd u))
    (kestenMcKayDensity_between_integrable d hd (by norm_num)
      (kestenMcKayClip_mem y).1 (kestenMcKayClip_mem y).2)

theorem kestenMcKayCDF_below (d : ℕ) (x : ℝ) (hx : x ≤ -2) :
    kestenMcKayCDF d x = 0 := by
  have hc : kestenMcKayClip x = -2 := by
    simp only [kestenMcKayClip, min_eq_right (by linarith : x ≤ 2), max_eq_left hx]
  simp only [kestenMcKayCDF, hc, intervalIntegral.integral_same]

theorem kestenMcKayCDF_above (d : ℕ) (hd : 3 ≤ d) (x : ℝ) (hx : 2 ≤ x) :
    kestenMcKayCDF d x = 1 := by
  have hc : kestenMcKayClip x = 2 := by
    simp only [kestenMcKayClip, min_eq_left hx, max_eq_right (by norm_num : (-2 : ℝ) ≤ 2)]
  simp only [kestenMcKayCDF, hc, kestenMcKayDensity_integral d hd]

theorem kestenMcKayCDF_sub (d : ℕ) (hd : 3 ≤ d) {x y : ℝ}
    (hx : -2 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2) :
    kestenMcKayCDF d y - kestenMcKayCDF d x =
      ∫ u in x..y, kestenMcKayDensity d u := by
  rw [kestenMcKayCDF, kestenMcKayCDF,
    kestenMcKayClip_eq ⟨hx, hxy.trans hy⟩, kestenMcKayClip_eq ⟨hx.trans hxy, hy⟩]
  have hh := intervalIntegral.integral_add_adjacent_intervals
    (kestenMcKayDensity_between_integrable d hd (by norm_num) hx (hxy.trans hy))
    (kestenMcKayDensity_between_integrable d hd hx hxy hy)
  linarith

/-- The middle half of an interval retains a uniform square-root density. -/
theorem kestenMcKayDensity_middle_lower (d : ℕ) (hd : 3 ≤ d) {x y u : ℝ}
    (hx : -2 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2)
    (hu : x + (y - x)/4 ≤ u ∧ u ≤ y - (y - x)/4) :
    Real.sqrt (y - x) / (6 * Real.pi) ≤ kestenMcKayDensity d u := by
  have hh : 0 ≤ y - x := by linarith
  have hu0 : -2 ≤ u := by linarith [hu.1]
  have hu1 : u ≤ 2 := by linarith [hu.2]
  have hrad : (y - x)/4 ≤ 4 - u^2 := by
    by_cases hupos : 0 ≤ u
    · have hm := mul_nonneg hupos (show 0 ≤ 2-u by linarith)
      nlinarith [hu.2]
    · have hm := mul_nonneg (show 0 ≤ -u by linarith) (show 0 ≤ 2+u by linarith)
      nlinarith [hu.1]
  have hs : Real.sqrt (y - x) / 2 ≤ Real.sqrt (4 - u^2) := by
    have hi := Real.sqrt_le_sqrt hrad
    rw [Real.sqrt_div hh] at hi
    norm_num at hi
    exact hi
  have hsemi : Real.sqrt (y - x) / (6 * Real.pi) ≤ (2/3 : ℝ) * semicircleDensity u := by
    unfold semicircleDensity
    calc
      _ = (2/3 : ℝ) * ((Real.sqrt (y-x) / 2) / (2 * Real.pi)) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hs (by positivity)) (by norm_num)
  exact hsemi.trans (kestenMcKayDensity_ge_semicircle d hd u)

theorem kestenMcKayDensity_interval_lower (d : ℕ) (hd : 3 ≤ d) {x y : ℝ}
    (hx : -2 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2) :
    (1 / (12 * Real.pi)) * (y-x) * Real.sqrt (y-x) ≤
      ∫ u in x..y, kestenMcKayDensity d u := by
  let a := x + (y-x)/4
  let b := y - (y-x)/4
  have hxa : x ≤ a := by dsimp only [a]; linarith
  have hab : a ≤ b := by dsimp only [a,b]; linarith
  have hby : b ≤ y := by dsimp only [b]; linarith
  have hi := kestenMcKayDensity_between_integrable d hd hx hxy hy
  have himid := kestenMcKayDensity_between_integrable d hd (hx.trans hxa) hab (hby.trans hy)
  have hpoint := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Real.sqrt (y-x)/(6*Real.pi)) volume a b)
    himid (fun u hu => kestenMcKayDensity_middle_lower d hd hx hxy hy hu)
  have hrestrict := intervalIntegral.integral_mono_interval hxa hab hby
    (ae_of_all _ (fun u => kestenMcKayDensity_nonnegative d hd u)) hi
  have hconst : (∫ _u in a..b, Real.sqrt (y-x)/(6*Real.pi)) =
      (1/(12*Real.pi))*(y-x)*Real.sqrt (y-x) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    dsimp only [a,b]
    field_simp
    ring
  rw [hconst] at hpoint
  exact hpoint.trans hrestrict

def kestenMcKayCompactCDF (d : ℕ) (hd : 3 ≤ d) : CompactCDF where
  lower := -2
  upper := 2
  proper := by norm_num
  cdf := kestenMcKayCDF d
  continuous := kestenMcKayCDF_continuous d hd
  monotone := kestenMcKayCDF_monotone d hd
  below := kestenMcKayCDF_below d
  above := kestenMcKayCDF_above d hd

def kestenMcKaySquareRootCDF (d : ℕ) (hd : 3 ≤ d) : SquareRootCDF where
  toCompactCDF := kestenMcKayCompactCDF d hd
  mass := 1 / (12 * Real.pi)
  mass_pos := by positivity
  lower_mass := by
    intro x y hx hxy hy
    change (1/(12*Real.pi))*(y-x)*Real.sqrt (y-x) ≤ kestenMcKayCDF d y-kestenMcKayCDF d x
    rw [kestenMcKayCDF_sub d hd hx hxy hy]
    exact kestenMcKayDensity_interval_lower d hd hx hxy hy

end SpectralConsequences
