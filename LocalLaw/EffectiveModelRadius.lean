import LocalLaw.LocalizationErrorBounds
import LocalLaw.UniformGraphNet
import LocalLaw.SharpSamplingCounts
import LocalLaw.RadiusHierarchy

/-!
# Shorter internal model radius with the original paper error

The nominal paper error and its inflation branch are kept unchanged. An
internal radius loses two upper log-log radii plus four edges, which supplies
the endpoint common-neighborhood margin. The resulting localization tail is
paid by the nominal error with a remaining (log N)^(-4a) gain.
-/

open Filter
noncomputable section
namespace LocalLaw

def modelRadiusLoss (a d N : ℕ) : ℕ := 2 * doubleLogRadius a d N + 4

def effectiveModelRadius (a d N : ℕ) (β : ℝ) : ℕ :=
  logarithmicRadius β d N - modelRadiusLoss a d N

/-- The exact integer loss costs only the stated logarithmic power. -/
theorem modelRadiusLoss_power_bound (a d N : ℕ) (hd : 3 ≤ d)
    (hlog : 1 ≤ Real.log (N : ℝ)) :
    (((d - 1 : ℕ) : ℝ) ^ modelRadiusLoss a d N) ≤
      (((d - 1 : ℕ) : ℝ) ^ 4) * Real.log (N : ℝ) ^ (4 * a) := by
  have hp := doubleLogRadius_base_power_bound a d N hd hlog
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ ((d - 1 : ℕ) : ℝ) ^ doubleLogRadius a d N) hp 2
  calc
    _ = (((d - 1 : ℕ) : ℝ) ^ 4) * (((d - 1 : ℕ) : ℝ) ^ doubleLogRadius a d N) ^ 2 := by
      unfold modelRadiusLoss
      rw [pow_add, pow_mul]
      ring
    _ ≤ (((d - 1 : ℕ) : ℝ) ^ 4) * (Real.log (N : ℝ) ^ (2 * a)) ^ 2 :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by
      rw [← pow_mul (Real.log (N : ℝ)) (2 * a) 2]
      congr 2
      omega

/-- A smaller internal model pays its tail using the NOMINAL paper error.
There is no comparison between two inflated-error branches. -/
theorem effectiveModelRadius_localization_tail (a d N : ℕ) (β : ℝ) (hd : 3 ≤ d)
    (hlog : 1 ≤ Real.log (N : ℝ))
    (hroom : modelRadiusLoss a d N ≤ logarithmicRadius β d N)
    (z : ℂ) (hz : 0 ≤ z.im) :
    physicalTransfer d z ^ (2 * effectiveModelRadius a d N β) ≤
      (((d - 1 : ℕ) : ℝ) ^ 4) * graphPaperError a d N (logarithmicRadius β d N) z /
        Real.log (N : ℝ) ^ (4 * a) := by
  let k : ℝ := ((d - 1 : ℕ) : ℝ)
  let L := Real.log (N : ℝ)
  let r := logarithmicRadius β d N
  let loss := modelRadiusLoss a d N
  let ε := graphPaperError a d N r z
  have hk : 0 < k := by dsimp only [k]; exact_mod_cast (show 0 < d - 1 by omega)
  have hL : 0 < L := by linarith
  have htail := physical_transfer_two_sided_tail d hd z (effectiveModelRadius a d N β)
  have hdecomp : (k ^ effectiveModelRadius a d N β)⁻¹ = k ^ loss * (k ^ r)⁻¹ := by
    unfold effectiveModelRadius
    rw [pow_sub₀ k (ne_of_gt hk) hroom, mul_inv_rev, inv_inv]
  have hcost := modelRadiusLoss_power_bound a d N hd hlog
  change k ^ loss ≤ k ^ 4 * L ^ (4 * a) at hcost
  have hε := graphPaperError_lower a d N r z hlog hz
  change L ^ (8 * a) * (k ^ r)⁻¹ ≤ ε at hε
  apply htail.trans
  change (k ^ effectiveModelRadius a d N β)⁻¹ ≤ _
  rw [hdecomp]
  apply (le_div_iff₀ (pow_pos hL _)).mpr
  have hfirst := mul_le_mul_of_nonneg_right hcost (by positivity : 0 ≤ (k ^ r)⁻¹)
  have hsecond := mul_le_mul_of_nonneg_right hfirst (pow_nonneg hL.le (4 * a))
  have hthird := mul_le_mul_of_nonneg_left hε (by positivity : 0 ≤ k ^ 4)
  calc
    _ ≤ (k ^ 4 * L ^ (4 * a)) * (k ^ r)⁻¹ * L ^ (4 * a) := hsecond
    _ = k ^ 4 * (L ^ (8 * a) * (k ^ r)⁻¹) := by
      have he : 8 * a = 4 * a + 4 * a := by omega
      rw [he, pow_add]
      ring
    _ ≤ _ := hthird

/-- The source endpoint beta=c/32 is included. Every selected radius-ell
common neighborhood has one extra edge of room below R/8. -/
theorem eventually_effectiveModelRadius_margins (a d : ℕ) (c β : ℝ)
    (ha : 0 < a) (hd : 3 ≤ d) (hc : 0 < c) (hβ : 0 < β) (hβc : β ≤ c / 32) :
    ∀ᶠ N : ℕ in atTop,
      modelRadiusLoss a d N ≤ logarithmicRadius β d N ∧
      1 ≤ effectiveModelRadius a d N β ∧
      effectiveModelRadius a d N β ≤ logarithmicRadius β d N ∧
      ∀ z : ℂ,
        effectiveModelRadius a d N β + (actualCavityDepth a d N z - 1) + 1 ≤
          logarithmicRadius (c / 4) d N / 8 := by
  have hdepth := (lowerLogLogRadius_tendsto a d ha hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_source_radius_hierarchy a d c β hd hc hβ hβc, hdepth]
    with N hradii hdepth
  have hroom : modelRadiusLoss a d N + 1 ≤ logarithmicRadius β d N := by
    have hh := hradii.2.1
    unfold modelRadiusLoss
    omega
  refine ⟨by omega, ?_, Nat.sub_le _ _, ?_⟩
  · unfold effectiveModelRadius
    omega
  · intro z
    have hell := (actualCavityDepth_radius_bounds a d N z hdepth).2
    have he := hradii.1
    unfold effectiveModelRadius modelRadiusLoss
    unfold modelRadiusLoss at hroom
    omega

/-- Finite common-ball margin with two full upper log-log radii. -/
theorem effectiveModelRadius_common_ball_margin (a d N : ℕ) (c β : ℝ)
    (hroom : modelRadiusLoss a d N ≤ logarithmicRadius β d N)
    (hR : 8 * logarithmicRadius β d N ≤ logarithmicRadius (c / 4) d N) :
    effectiveModelRadius a d N β + 2 * doubleLogRadius a d N + 1 ≤
      logarithmicRadius (c / 4) d N / 8 := by
  unfold effectiveModelRadius modelRadiusLoss at *
  omega

/-- The stronger common-ball margin is realized also at beta=c/32. -/
theorem eventually_effectiveModelRadius_common_ball_margin (a d : ℕ) (c β : ℝ)
    (hd : 3 ≤ d) (hc : 0 < c) (hβ : 0 < β) (hβc : β ≤ c / 32) :
    ∀ᶠ N : ℕ in atTop,
      effectiveModelRadius a d N β + 2 * doubleLogRadius a d N + 1 ≤
        logarithmicRadius (c / 4) d N / 8 := by
  filter_upwards [eventually_source_radius_hierarchy a d c β hd hc hβ hβc] with N hradii
  apply effectiveModelRadius_common_ball_margin a d N c β _ hradii.1
  have hh := hradii.2.1
  unfold modelRadiusLoss
  omega

end LocalLaw
