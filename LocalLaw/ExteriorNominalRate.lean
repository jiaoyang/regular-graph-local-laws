import LocalLaw.ExteriorRate
import LocalLaw.SparseParameterAbsorption
import LocalLaw.ParameterSmallness

/-! # The nominal physical-reference local law on the entire unbounded exterior -/

namespace LocalLaw
namespace RegularGraph
variable {N d : ℕ}

theorem exterior_reference_entry_trace_local_law (g : RegularGraph N d) (hN : 0 < N) (hd : 3 ≤ d)
    (r R : ℕ) (hR : r ≤ R) (z : ℂ) (hzIm : 0 < z.im) (hz : 2 * (d : ℝ) ≤ ‖z‖)
    (ε M : ℝ) (hM : 0 ≤ M)
    (hbad : ((nonTreeCenters g.graph R).card : ℝ) / (N : ℝ) ≤
      M * (1 / (((d : ℝ) - 1) ^ r)))
    (hbudget : 2 * (1 / (((d : ℝ) - 1) ^ r)) ≤ ε) (hε : ε ≤ 1) :
    (∀ i j, ‖g.G z i j - g.P r z (semicircleRoot z) i j‖ ≤ scalarScale (spectralScale z) ε) ∧
      ‖empiricalTransform g.H z - graphKestenMcKayReference d z‖ ≤
        (1 + 3 * M) * scalarScale (spectralScale z) ε := by
  constructor
  · intro i j
    have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
    have hk : 0 ≤ (d : ℝ) - 1 := by linarith
    have hh := g.exterior_pair_approximation_spectral hd r z (semicircleRoot z)
      (semicircleRoot_norm_le_one z) hz i j
    exact hh.trans (exterior_spectral_rate_le_scalarScale z hzIm (by
      have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
      linarith) _ ε (by positivity) hbudget hε)
  · exact g.exterior_trace_local_law hN hd r R hR z hzIm hz ε M hM hbad hbudget hε

theorem eventually_exterior_actual_nominal_local_law (a b d : ℕ) (β γ : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hβ : 0 < β) (hexp : γ + β ≤ 1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (R : ℕ),
      logarithmicRadius β d N ≤ R → ((nonTreeCenters g.graph R).card : ℝ) ≤ (N : ℝ) ^ γ →
      ∀ z : ℂ, 0 < z.im → 2 * (d : ℝ) ≤ ‖z‖ → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ActualGraphLocalLawAt a (logarithmicRadius β d N) 1 4 z g := by
  filter_upwards [eventually_paperError_small a b d β ha hb hd hβ,
    eventually_log_ge_nat 2, Filter.eventually_ge_atTop 1] with N herror hlog hN
  intro g R hR hbad z hzIm hz hfloor
  let r := logarithmicRadius β d N
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N r z
  let δ := ((((d - 1 : ℕ) : ℝ) ^ r))⁻¹
  have hLp : 0 < L := by dsimp only [L]; linarith
  have hLone : 1 ≤ L := by dsimp only [L]; linarith
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hraw := (baseError_component_bounds L a d N r z.im
    (graphKestenMcKayReference d z).im hLp.le hzIm.le).1
  have hinflate := (inflateError_bounds (s := spectralScale z) hLone
    (baseError_nonnegative L a d N r z.im (graphKestenMcKayReference d z).im hLp.le hzIm.le)).1
  have hgain : 2 ≤ L ^ (8 * a) := hlog.trans
    (by simpa only [pow_one] using pow_le_pow_right₀ hLone (show 1 ≤ 8 * a by omega))
  have hbudgetNat : 2 * δ ≤ ε :=
    (mul_le_mul_of_nonneg_right hgain hδ).trans (hraw.trans hinflate)
  have hsmall : ε ≤ 1 := (herror z hzIm hfloor).trans
    (inv_le_one_of_one_le₀ (one_le_pow₀ hLone))
  have hdensity := sparse_density_le_localization N d β γ (nonTreeCenters g.graph R).card hN hd hβ.le hexp hbad
  have hk : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hbudget : 2 * (1 / (((d : ℝ) - 1) ^ r)) ≤ ε := by
    simpa only [δ, hk, one_div] using hbudgetNat
  have hdensity' : ((nonTreeCenters g.graph R).card : ℝ) / (N : ℝ) ≤
      1 * (1 / (((d : ℝ) - 1) ^ r)) := by simpa only [hk, one_div, one_mul] using hdensity
  have hh := g.exterior_reference_entry_trace_local_law (by omega) hd r R hR z hzIm hz ε 1
    (by norm_num) hdensity' hbudget hsmall
  constructor
  · simpa only [one_mul] using hh.1
  · simpa only [mul_one, one_mul, show (1 + (3 : ℝ)) = 4 by norm_num] using hh.2

end RegularGraph
end LocalLaw
