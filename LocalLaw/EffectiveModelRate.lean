import LocalLaw.IndependentRadiusModelTransfer

/-!
# Recover the nominal local law from the shorter internal model

The bootstrap may use the effective model radius with the unchanged nominal
paper error. Actual physical-reference localization corrects back to the
nominal pair model. Its logarithmic gain absorbs the correction into one
additional square-root stability tolerance.
-/

noncomputable section
namespace LocalLaw
local instance effectiveModelRateDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem referenceRadiusConstant_nonnegative (d : ℕ) (hd : 3 ≤ d) : 0 ≤ referenceRadiusConstant d := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hk : 0 < (d : ℝ) - 1 := by linarith
  have hExtra : 0 ≤ finiteExtraReferenceConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans
    (finiteExtraReferenceConstant_ge_one d hd)
  unfold referenceRadiusConstant DeficientGraph.localizationExceptionalMass
  positivity

namespace RegularGraph

/-- The original nominal-radius entry and trace conclusions follow from the
effective-radius weak event, with every reference correction and numerical
absorption proved. This includes the endpoint beta=c/32. -/
theorem eventually_actual_nominal_local_law_of_effective_weak (a b d : ℕ) (c β γ B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hγβ : γ + β ≤ 1) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      offsetStructural (logarithmicRadius (c / 4) d N) (finiteOmega d) 1 ⌊(N : ℝ) ^ γ⌋₊ g →
      (graphLocalLawFamilyWithRadii N d a (effectiveModelRadius a d N β)
        (logarithmicRadius β d N)).weak z g →
      ActualGraphLocalLawAt a (logarithmicRadius β d N)
        (sourceWidthConstant B + pairSensitivityConstant d + 1)
        (sourceWidthConstant B + pairSensitivityConstant d + 1) z g := by
  let A := sourceWidthConstant B
  let K := referenceRadiusConstant d * (((d - 1 : ℕ) : ℝ) ^ 4)
  have hA : 0 < A := sourceWidthConstant_pos B hB
  have hK : 0 ≤ K := mul_nonneg (referenceRadiusConstant_nonnegative d hd) (by positivity)
  filter_upwards [eventually_actual_local_law_with_radii_of_source_weak a b d c β γ B
      ha hb hd hc hβ hβc hγβ hB,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_source_radius_hierarchy a d c β hd hc hβ hβc,
    eventually_paperError_small a b d β ha hb hd hβ,
    eventually_log_ge_nat 1, eventually_log_ge_nat (A * K), Filter.eventually_ge_atTop 1]
    with N htransfer heffective hradii herror hlog hconstant hN
  intro g z hz hzB hscale haux hweak
  let r := logarithmicRadius β d N
  let reff := effectiveModelRadius a d N β
  let R := logarithmicRadius (c / 4) d N
  let ε := graphPaperError a d N r z
  let Ψ := scalarScale (spectralScale z) ε
  have hlocal := htransfer reff heffective.2.2.1 g z hz hzB hscale haux hweak
  have hstruct := offsetStructural_implies_structural haux
  have hmargin : 4 * r + 1 ≤ R := by
    have he := hradii.1
    have hl := hradii.2.1
    dsimp only [r, R]
    omega
  have href := g.effective_reference_radius_correction hd a β R hmargin hstruct.1 hlog heffective.1 z hz
  have hεnonneg : 0 ≤ ε := graphPaperError_nonnegative a d N r z hN hz.le
  have hεone : ε ≤ 1 := by
    exact (herror z hz hscale).trans (inv_le_one_of_one_le₀ (one_le_pow₀ hlog))
  have hwidth : Real.sqrt (spectralScale z + ε) ≤ A := source_bounded_width B z ε hzB hεone
  have hidentity : ε = Ψ * Real.sqrt (spectralScale z + ε) := by
    have hroot : 0 < Real.sqrt (spectralScale z + ε) :=
      Real.sqrt_pos.mpr (by linarith [spectralScale_pos hz])
    dsimp only [Ψ, scalarScale]
    field_simp
  have hpow : A * K ≤ Real.log (N : ℝ) ^ (4 * a) := by
    exact hconstant.trans (by simpa only [pow_one] using pow_le_pow_right₀ hlog (show 1 ≤ 4 * a by omega))
  have hcorr : K * ε / Real.log (N : ℝ) ^ (4 * a) ≤ Ψ := by
    have hlogp : 0 < Real.log (N : ℝ) := by linarith
    apply le_trans _ (show ε / A ≤ Ψ from ?_)
    · apply (div_le_div_iff₀ (pow_pos hlogp _) hA).mpr
      have hh := mul_le_mul_of_nonneg_right hpow hεnonneg
      nlinarith
    · apply (div_le_iff₀ hA).mpr
      rw [hidentity]
      exact mul_le_mul_of_nonneg_left hwidth (scalarScale_nonneg hεnonneg)
  constructor
  · intro i j
    have ht := norm_sub_le_norm_sub_add_norm_sub (g.G z i j)
      (g.P reff z (semicircleRoot z) i j) (g.P r z (semicircleRoot z) i j)
    have hreference : ‖g.P reff z (semicircleRoot z) i j - g.P r z (semicircleRoot z) i j‖ ≤ Ψ := by
      have hh := href i j
      change ‖g.P r z (semicircleRoot z) i j - g.P reff z (semicircleRoot z) i j‖ ≤
        K * ε / Real.log (N : ℝ) ^ (4 * a) at hh
      have hh' : ‖g.P reff z (semicircleRoot z) i j - g.P r z (semicircleRoot z) i j‖ ≤
          K * ε / Real.log (N : ℝ) ^ (4 * a) := by
        simpa only [norm_sub_rev] using hh
      exact hh'.trans hcorr
    apply ht.trans ((add_le_add (hlocal.1 i j) hreference).trans_eq ?_)
    ring
  · exact hlocal.2

end RegularGraph
end LocalLaw
