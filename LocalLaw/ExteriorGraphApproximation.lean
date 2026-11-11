import LocalLaw.GraphPowerLocality
import LocalLaw.ExteriorLocalization

/-!
# Actual exterior localization for regular graphs

Finite moment matching connects the physical graph resolvent with its genuine
finite pair-neighborhood extension. The resulting bound is the deterministic
localization part of the large-|z| anchor, with no tree-like geometry assumed.
-/

open scoped BigOperators

namespace LocalLaw

/-- The common exterior moment-matching error at order 2r+1 is at most
(d-1)^(-r), with an explicit finite-N-free constant one. -/
theorem normalized_exterior_localization_rate (d : ℕ) (hd : 3 ≤ d) (z : ℂ)
    (hz : 2 * (d : ℝ) ≤ ‖z‖) (r : ℕ) :
    let M := (d : ℝ) / Real.sqrt ((d : ℝ) - 1)
    2 * (M / ‖z‖) ^ (2 * r + 1) / (‖z‖ - M) ≤ 1 / (((d : ℝ) - 1) ^ r) := by
  obtain ⟨hM, hgap, hden, hratio⟩ := normalized_exterior_constants d hd z hz
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hkpos : 0 < (d : ℝ) - 1 := by linarith
  have hspos : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr hkpos
  have hsone : 1 ≤ Real.sqrt ((d : ℝ) - 1) := by
    have hh := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ d - 1 by linarith)
    simpa only [Real.sqrt_one] using hh
  let ρ := ((d : ℝ) / Real.sqrt ((d : ℝ) - 1)) / ‖z‖
  have hρ0 : 0 ≤ ρ := div_nonneg hM (norm_nonneg _)
  have hρsqrt : ρ ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹ := by
    exact hratio.trans (by
      rw [← one_div]
      exact one_div_le_one_div_of_le hspos (by linarith))
  have hρone : ρ ≤ 1 := hρsqrt.trans (by
    rw [← one_div]
    exact (div_le_one hspos).mpr hsone)
  have hbase : ρ ^ 2 ≤ 1 / ((d : ℝ) - 1) := by
    have hp := pow_le_pow_left₀ hρ0 hρsqrt 2
    rwa [inv_pow, Real.sq_sqrt hkpos.le, ← one_div] at hp
  have hpow : ρ ^ (2 * r + 1) ≤ (1 / ((d : ℝ) - 1)) ^ r := by
    calc
      ρ ^ (2 * r + 1) = (ρ ^ 2) ^ r * ρ := by rw [pow_add, pow_one, pow_mul]
      _ ≤ (1 / ((d : ℝ) - 1)) ^ r * 1 :=
        mul_le_mul (pow_le_pow_left₀ (sq_nonneg _) hbase r) hρone hρ0 (by positivity)
      _ = (1 / ((d : ℝ) - 1)) ^ r := mul_one _
  have hgapPos : 0 < ‖z‖ - (d : ℝ) / Real.sqrt ((d : ℝ) - 1) := sub_pos.mpr hgap
  have hfactor : 2 / (‖z‖ - (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) ≤ 1 := by
    apply (div_le_one hgapPos).mpr
    linarith
  change 2 * ρ ^ (2 * r + 1) / (‖z‖ - (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) ≤ _
  calc
    _ = (2 / (‖z‖ - (d : ℝ) / Real.sqrt ((d : ℝ) - 1))) * ρ ^ (2 * r + 1) := by ring
    _ ≤ 1 * (1 / ((d : ℝ) - 1)) ^ r :=
      mul_le_mul hfactor hpow (pow_nonneg hρ0 _) (by norm_num)
    _ = 1 / (((d : ℝ) - 1) ^ r) := by rw [one_mul, one_div_pow]

noncomputable section
local instance exteriorApproxDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace RegularGraph
variable {N d : ℕ}

/-- Deterministic exterior localization for the actual pair-neighborhood
extension, valid for every boundary weight with norm at most one. -/
theorem exterior_pair_approximation (g : RegularGraph N d) (hd : 3 ≤ d)
    (r : ℕ) (z w : ℂ) (hw : ‖w‖ ≤ 1) (hz : 2 * (d : ℝ) ≤ ‖z‖) (i j : Fin N) :
    ‖g.G z i j - g.P r z w i j‖ ≤ 1 / (((d : ℝ) - 1) ^ r) := by
  obtain ⟨hM, hgap, _, _⟩ := normalized_exterior_constants d hd z hz
  have hHrow : ∀ v, ∑ u, ‖g.H v u‖ ≤ (d : ℝ) / Real.sqrt ((d : ℝ) - 1) := by
    intro v
    rw [H, normalizedAdjacency_row_sum, g.regular v]
  have hBrow := g.pairExtension_row_sum_bound hd r w hw i j
  have hmoments : ∀ n < 2 * r + 1, (g.H ^ n) i j =
      (g.pairExtensionMatrix r w i j ^ n) (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r) := by
    intro n hn
    exact g.pairExtension_power_eq r w i j n (by omega)
  have hbound := resolvent_moment_matching_bound g.H (g.pairExtensionMatrix r w i j)
    z _ hM hHrow hBrow hgap (2 * r + 1) i j
    (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r) hmoments
  rw [g.P_eq_green_pairExtension]
  exact hbound.trans (normalized_exterior_localization_rate d hd z hz r)

/-- In particular the semicircle-boundary local model gives the deterministic
source estimate (4.22), with the positive stochastic terms unnecessary here. -/
theorem exterior_reference_approximation (g : RegularGraph N d) (hd : 3 ≤ d)
    (r : ℕ) (z : ℂ) (hz : 2 * (d : ℝ) ≤ ‖z‖) (i j : Fin N) :
    ‖g.G z i j - g.P r z (semicircleRoot z) i j‖ ≤ 1 / (((d : ℝ) - 1) ^ r) :=
  g.exterior_pair_approximation hd r z (semicircleRoot z) (semicircleRoot_norm_le_one z) hz i j

end RegularGraph
end

end LocalLaw
