import LocalLaw.EndpointSurgeryParameters
import LocalLaw.ParameterCorrelation

/-!
# Realized actual correlation and quadratic surgery corrections

The actual inflation branch supplies phi <= epsilon/log^(4a). Together with
the literal endpoint count, all finite diagonal surgery corrections fit the
nominal sixteen-log tolerance, uniformly above the source spectral floor.
-/

noncomputable section
namespace LocalLaw
local instance sourceSurgeryCorrectionsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem sourceCorrelationThreshold_le_error (a b d N r : ℕ) (z : ℂ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hN : 0 < N) (hz : 0 < z.im)
    (hL : 9 ≤ Real.log (N : ℝ))
    (hscale : Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im) :
    correlationThreshold (Real.log (N : ℝ)) a N z.im (graphKestenMcKayReference d z).im
      (spectralScale z) (graphPaperError a d N r z) ≤
        graphPaperError a d N r z / Real.log (N : ℝ) ^ (4 * a) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsample : Real.log (N : ℝ) ^ b ≤ (N : ℝ) * z.im := by
    have hh := (div_le_iff₀ hn).mp hscale
    simpa only [mul_comm] using hh
  have hv : 0 ≤ (graphKestenMcKayReference d z).im :=
    (kestenMcKayTransform_im_pos d (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le).le
  exact correlationThreshold_le_inflated_base (Real.log (N : ℝ)) a b d N r z.im
    (graphKestenMcKayReference d z).im (spectralScale z) hL ha hb hN hz hv (spectralScale_pos hz) hsample

namespace RegularGraph

/-- The actual finite-rank diagonal error budget, with the actual phi and
nominal epsilon, holds for every source endpoint count eventually. -/
theorem eventually_source_surgery_diagonal_correction_small (a b d : ℕ) (β D K : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hβ : 0 < β) (hD : 0 ≤ D) (hK : 0 ≤ K) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (ell n : ℕ),
      ell ≤ doubleLogRadius a d N →
      n ≤ 3 * Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) →
      ∀ z : ℂ, 0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      K * ((D * g.sourcePrime a (logarithmicRadius β d N) z) ^ 2 + (n : ℝ) *
        correlationThreshold (Real.log (N : ℝ)) a N z.im (graphKestenMcKayReference d z).im
          (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z)) ≤
        graphPaperError a d N (logarithmicRadius β d N) z / Real.log (N : ℝ) ^ 16 := by
  let U : ℝ := 3 * (d : ℝ) * ((d : ℝ) + 1)
  filter_upwards [eventually_paperError_small a b d β ha hb hd hβ, eventually_log_ge_nat 9,
    eventually_log_ge_nat (2 * K * D ^ 2), eventually_log_ge_nat (2 * K * U),
    Filter.eventually_ge_atTop 1] with N hsmall hL hlargeSquare hlargeDensity hN
  intro g o ell n hell hn z hz hscale
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith
  have hε : 0 ≤ ε := graphPaperError_nonnegative a d N _ z hN hz.le
  have hcap : ε * L ^ (4 * a) ≤ 1 :=
    (le_div_iff₀ (pow_pos (by linarith : 0 < L) _)).mp
      (by simpa only [one_div] using hsmall z hz hscale)
  have hcount : (n : ℝ) ≤ U * L ^ (2 * a) := by
    have hreal : (n : ℝ) ≤ 3 * (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) := by exact_mod_cast hn
    have hh := mul_le_mul_of_nonneg_left (g.boundary_card_log_bound o a ell hd hL1 hell) (by norm_num : (0 : ℝ) ≤ 3)
    exact hreal.trans (hh.trans_eq (by dsimp only [U]; ring))
  have hφ : φ ≤ ε / L ^ (4 * a) := sourceCorrelationThreshold_le_error a b d N _ z ha hb
    (by omega) hz hL hscale
  have hh := source_surgery_diagonal_correction_absorption a L ε (n : ℝ) U D K φ ha hL1 hε
    (Nat.cast_nonneg n) (by dsimp only [U]; positivity) hD hK hcap hcount hφ hlargeSquare hlargeDensity
  convert hh using 1
  unfold sourcePrime inflatedPrime
  ring

end RegularGraph
end LocalLaw
