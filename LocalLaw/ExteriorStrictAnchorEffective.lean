import LocalLaw.ExteriorStrictAnchor
import LocalLaw.EffectiveModelRadius
import LocalLaw.IndependentRadiusEvents

/-!
# Strict exterior seeds with independent model and error radii

The internal effective radius is shorter by the proved logarithmic loss,
while the actual error and its inflation branch remain at the nominal
radius. Its geometric localization error is paid directly by the nominal
error floor. No comparison of two inflated paper errors is used.
-/

open Filter
noncomputable section
namespace LocalLaw
local instance exteriorStrictEffectiveDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The actual geometric error at the shorter radius is paid by the nominal
paper error with a remaining logarithmic gain. -/
theorem effectiveModelRadius_geometric_error (a d N : ℕ) (β : ℝ) (hd : 3 ≤ d)
    (hlog : 1 ≤ Real.log (N : ℝ))
    (hroom : modelRadiusLoss a d N ≤ logarithmicRadius β d N) (z : ℂ) (hz : 0 ≤ z.im) :
    ((((d - 1 : ℕ) : ℝ) ^ effectiveModelRadius a d N β)⁻¹) ≤
      (((d - 1 : ℕ) : ℝ) ^ 4) * graphPaperError a d N (logarithmicRadius β d N) z /
        Real.log (N : ℝ) ^ (4 * a) := by
  let k : ℝ := ((d - 1 : ℕ) : ℝ)
  let L := Real.log (N : ℝ)
  let r := logarithmicRadius β d N
  let loss := modelRadiusLoss a d N
  let ε := graphPaperError a d N r z
  have hk : 0 < k := by dsimp only [k]; exact_mod_cast (show 0 < d - 1 by omega)
  have hL : 0 < L := by linarith
  have hdecomp : (k ^ effectiveModelRadius a d N β)⁻¹ = k ^ loss * (k ^ r)⁻¹ := by
    unfold effectiveModelRadius
    rw [pow_sub₀ k (ne_of_gt hk) hroom, mul_inv_rev, inv_inv]
  have hcost := modelRadiusLoss_power_bound a d N hd hlog
  change k ^ loss ≤ k ^ 4 * L ^ (4 * a) at hcost
  have hε := graphPaperError_lower a d N r z hlog hz
  change L ^ (8 * a) * (k ^ r)⁻¹ ≤ ε at hε
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

theorem exterior_geometric_error_absorption (δ ε K P D : ℝ)
    (hP : 0 < P) (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (herror : δ ≤ K * ε / P) (hgain : D * K ≤ P) : D * δ ≤ ε := by
  have hh := mul_le_mul_of_nonneg_right hgain hε
  calc
    _ ≤ D * (K * ε / P) := mul_le_mul_of_nonneg_left herror hD
    _ = (D * K) * ε / P := by ring
    _ ≤ ε := (div_le_iff₀ hP).mpr (by nlinarith only [hh])

namespace RegularGraph
variable {N d : ℕ}

/-- Finite actual strict exterior anchor, with model and nominal error
radii independent. Its two paid-error inequalities are purely numerical. -/
theorem exterior_strict_anchor_with_radii (g : RegularGraph N d) (hN : 0 < N) (hd : 3 ≤ d)
    (a rModel rError R : ℕ) (hR : rModel + 1 ≤ R) (z : ℂ) (hzIm : 0 < z.im)
    (hz : 2 * (d : ℝ) ≤ ‖z‖) (B : ℝ) (hB : 0 ≤ B) (hzB : ‖z‖ ≤ B)
    (hlocal : 1 / (((d : ℝ) - 1) ^ rModel) ≤ 1 / (2 * (B + 2)))
    (hbad : ((nonTreeCenters g.graph R).card : ℝ) / (N : ℝ) ≤ 1 / (((d : ℝ) - 1) ^ rModel))
    (hpaidQ : 2 * (3 + 6 * (B + 2)) * Real.sqrt (2 * B + 3) *
      (1 / (((d : ℝ) - 1) ^ rModel)) ≤ graphPaperError a d N rError z)
    (hpaidEntry : 2 * (1 / (((d : ℝ) - 1) ^ rModel)) ≤ graphPaperError a d N rError z)
    (hsmall : graphPaperError a d N rError z ≤ 1) :
    (graphLocalLawFamilyWithRadii N d a rModel rError).strict z g := by
  let δ := 1 / (((d : ℝ) - 1) ^ rModel)
  let ε := graphPaperError a d N rError z
  let C := 3 + 6 * (B + 2)
  let A := Real.sqrt (2 * B + 3)
  have hε : 0 ≤ ε := graphPaperError_nonnegative a d N rError z (by omega) hzIm.le
  have hA : 0 < A := by dsimp only [A]; positivity
  have hroot : 0 < Real.sqrt (spectralScale z + ε) :=
    Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (spectralScale_pos hzIm) hε)
  have hcap : Real.sqrt (spectralScale z + ε) ≤ A := by
    apply Real.sqrt_le_sqrt
    have hh := spectralScale_le_twice_norm_add_two z
    change spectralScale z + graphPaperError a d N rError z ≤ 2 * B + 3
    linarith
  have hbudget : C * δ ≤ scalarScale (spectralScale z) ε / 2 := by
    have hh : 2 * C * δ ≤ ε / A := by
      apply (le_div_iff₀ hA).mpr
      convert hpaidQ using 1
      dsimp only [C, δ, A]
      ring
    have hdiv : ε / A ≤ scalarScale (spectralScale z) ε := by
      exact div_le_div₀ hε le_rfl hroot hcap
    linarith
  change ‖g.Q z - semicircleRoot z‖ ≤ scalarScale (spectralScale z) ε / 2 ∧
    ∀ i j, ‖g.G z i j - g.P rModel z (g.Q z) i j‖ ≤ ε / 2
  constructor
  · have hq := g.Q_exterior_anchor hN hd rModel R hR z hzIm hz B hzB hlocal
    have hq' : ‖g.Q z - semicircleRoot z‖ ≤ C * δ := by
      exact hq.trans ((add_le_add_left (mul_le_mul_of_nonneg_right hbad (by norm_num)) _).trans_eq
        (by dsimp only [C, δ]; ring))
    exact hq'.trans hbudget
  · intro i j
    exact (g.exterior_Q_reference_approximation hN hd rModel z hz i j).trans (by linarith only [hpaidEntry])

end RegularGraph

/-- Actual endpoint-compatible exterior strict seed at the effective model
radius and nominal paper error. Only the original exceptional-center count
and its source exponent condition remain geometric inputs. -/
theorem eventually_exterior_strict_anchor_with_radii (a b d : ℕ) (c β γ B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c) (hβ : 0 < β)
    (hβc : β ≤ c / 32) (hexp : γ + β ≤ 1) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in atTop, ∀ (g : RegularGraph N d) (R : ℕ),
      effectiveModelRadius a d N β + 1 ≤ R →
      ((nonTreeCenters g.graph R).card : ℝ) ≤ (N : ℝ) ^ γ →
      ∀ z : ℂ, 2 * (d : ℝ) ≤ ‖z‖ → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      (graphLocalLawFamilyWithRadii N d a (effectiveModelRadius a d N β)
        (logarithmicRadius β d N)).strict z g := by
  let k : ℝ := ((d - 1 : ℕ) : ℝ)
  let C := 2 * (3 + 6 * (B + 2)) * Real.sqrt (2 * B + 3)
  let D := max (2 * (B + 2)) (max C 2)
  have hk : 1 < k := by dsimp only [k]; exact_mod_cast (show 1 < d - 1 by omega)
  have hkcast : k = (d : ℝ) - 1 := by dsimp only [k]; rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hD : 0 ≤ D := (by positivity : (0 : ℝ) ≤ 2 * (B + 2)).trans (le_max_left _ _)
  filter_upwards [eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_paperError_small a b d β ha hb hd hβ,
    eventually_log_ge_nat 1, eventually_log_ge_nat (D * k ^ 4), eventually_ge_atTop 1]
    with N hradii herr hlog hlarge hN
  intro g R hR hbad z hz hzB hfloor
  let L := Real.log (N : ℝ)
  let r := effectiveModelRadius a d N β
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let δ := (k ^ r)⁻¹
  have hNpos : 0 < N := by omega
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hLp : 0 < L := by linarith
  have hzIm : 0 < z.im := (div_pos (pow_pos hLp _) hNp).trans_le hfloor
  have hε : 0 ≤ ε := graphPaperError_nonnegative a d N _ z hN hzIm.le
  have herror := effectiveModelRadius_geometric_error a d N β hd hlog hradii.1 z hzIm.le
  have hgain : D * k ^ 4 ≤ L ^ (4 * a) := hlarge.trans
    (by simpa only [pow_one] using pow_le_pow_right₀ hlog (show 1 ≤ 4 * a by omega))
  have hpaid : D * δ ≤ ε := exterior_geometric_error_absorption δ ε (k ^ 4) (L ^ (4 * a)) D
    (pow_pos hLp _) hε hD herror hgain
  have hsmall : ε ≤ 1 := (herr z hzIm hfloor).trans
    ((inv_le_one₀ (pow_pos hLp _)).mpr (one_le_pow₀ hlog))
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hlocal : δ ≤ 1 / (2 * (B + 2)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (B + 2))).mpr
    have hh := (mul_le_mul_of_nonneg_right (le_max_left (2 * (B + 2)) (max C 2)) hδ).trans hpaid
    nlinarith only [hh, hsmall]
  have hpaidQ : C * δ ≤ ε :=
    (mul_le_mul_of_nonneg_right ((le_max_left C 2).trans (le_max_right _ _)) hδ).trans hpaid
  have hpaidEntry : 2 * δ ≤ ε :=
    (mul_le_mul_of_nonneg_right ((le_max_right C 2).trans (le_max_right _ _)) hδ).trans hpaid
  have hdensity := sparse_density_le_localization N d β γ (nonTreeCenters g.graph R).card
    hN hd hβ.le hexp hbad
  have hpow := pow_le_pow_right₀ hk.le hradii.2.2.1
  have htailmono : (k ^ logarithmicRadius β d N)⁻¹ ≤ δ := by
    exact inv_anti₀ (pow_pos (lt_trans (by norm_num : (0 : ℝ) < 1) hk) _) hpow
  have hdensity' : ((nonTreeCenters g.graph R).card : ℝ) / (N : ℝ) ≤ δ := hdensity.trans htailmono
  apply g.exterior_strict_anchor_with_radii hNpos hd a r (logarithmicRadius β d N) R hR z hzIm hz B hB hzB
  · simpa only [δ, hkcast, one_div] using hlocal
  · simpa only [δ, hkcast, one_div] using hdensity'
  · simpa only [C, δ, hkcast, one_div] using hpaidQ
  · simpa only [δ, hkcast, one_div] using hpaidEntry
  · exact hsmall

end LocalLaw
