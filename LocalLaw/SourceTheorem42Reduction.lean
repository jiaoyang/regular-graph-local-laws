import LocalLaw.SourceOriginalConditionalReduction

/-! # The original reference identifiers and real exponents, conditional only on stage one

This intermediate reduction takes the all-polynomial first resampling-stage
estimate as an explicit hypothesis. `SourceFirstStageProof` proves that
estimate, and `SourceTheorem42` applies the reduction. All spectral domains,
auxiliary-event losses, source structural conditioning, real exponent
rounding, density Stieltjes transforms and literal infinite tree-extension
Green entries are connected to the conclusion here.
-/

noncomputable section
namespace LocalLaw
local instance sourceTheorem42ReductionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem source_theorem_4_2_of_first_stage (d ω : ℕ) (a b c β : ℝ)
    (hd : 3 ≤ d) (hω : 1 ≤ ω)
    (hreference : SourceFiniteCoreReferenceThreshold d ω (by omega))
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hc : 0 < c) (hc₁ : c < 1)
    (hβ : 0 < β) (hβc : β ≤ c / 32)
    (hfirst : SourceFirstStageAllPowers ⌊a⌋₊ (25 * ⌊a⌋₊) d c β (7 * c / 8) (4 * d)) :
    ∀ D : ℕ, ∀ᶠ N : ℕ in Filter.atTop, Nonempty (RegularGraph N d) →
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        RegularGraph.structural (logarithmicRadius (c / 4) d N) ω ⌊(N : ℝ) ^ c⌋₊ g ∧
          ¬∀ z : ℂ, 0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
            RealSourceLocalLawAt (by omega) a (logarithmicRadius β d N) (sourceUniformLawConstant d) z g) /
        eventMass (RegularGraph.weight (N := N) (d := d))
          (RegularGraph.structural (logarithmicRadius (c / 4) d N) ω ⌊(N : ℝ) ^ c⌋₊) ≤
        1 / (N : ℝ) ^ D := by
  have ha0 : 0 ≤ a := by linarith
  have hA : 12 ≤ ⌊a⌋₊ := (Nat.le_floor_iff ha0).mpr ha
  have hωmax : ω ≤ finiteOmega d := source_reference_threshold_le_finiteOmega d ω hd hreference
  have hγ : 3 * c / 4 < 7 * c / 8 := by linarith
  have hgap : 7 * c / 8 + β < 1 := by linarith
  have hC : 0 ≤ sourceUniformLawConstant d := (by norm_num : (0 : ℝ) ≤ 4).trans
    (sourceUniformLawConstant_ge_four d)
  intro D
  filter_upwards [eventually_source_nominal_conditional_of_first_stage ⌊a⌋₊ (25 * ⌊a⌋₊) d ω D c β (7 * c / 8)
      hA le_rfl hd hω hωmax hc hc₁ hβ hβc hγ hgap hfirst,
    eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1] with N hnat hlog hN
  intro hnonempty
  have hpoint : ∀ g : RegularGraph N d,
      (∀ z : ℂ, 0 < z.im → Real.log (N : ℝ) ^ (25 * ⌊a⌋₊ : ℕ) / (N : ℝ) ≤ z.im →
        ActualGraphLocalLawAt ⌊a⌋₊ (logarithmicRadius β d N) (sourceUniformLawConstant d)
          (sourceUniformLawConstant d) z g) →
      ∀ z : ℂ, 0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
        RealSourceLocalLawAt (by omega) a (logarithmicRadius β d N) (sourceUniformLawConstant d) z g := by
    intro g hall z hz hfloor
    have hzNat := real_domain_implies_rounded_domain a b N z ha hb hlog hfloor
    have hreal := (hall z hz hzNat).to_real_exponent hN hlog hz (Nat.floor_le ha0) hC hC
    exact hreal.to_source hd hz
  have hmono : eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
      RegularGraph.structural (logarithmicRadius (c / 4) d N) ω ⌊(N : ℝ) ^ c⌋₊ g ∧
        ¬∀ z : ℂ, 0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
          RealSourceLocalLawAt (by omega) a (logarithmicRadius β d N) (sourceUniformLawConstant d) z g) ≤
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        RegularGraph.structural (logarithmicRadius (c / 4) d N) ω ⌊(N : ℝ) ^ c⌋₊ g ∧
          ¬∀ z : ℂ, 0 < z.im → Real.log (N : ℝ) ^ (25 * ⌊a⌋₊ : ℕ) / (N : ℝ) ≤ z.im →
            ActualGraphLocalLawAt ⌊a⌋₊ (logarithmicRadius β d N) (sourceUniformLawConstant d)
              (sourceUniformLawConstant d) z g) := by
    apply eventMass_mono RegularGraph.weight RegularGraph.weight_nonnegative
    intro g hg
    exact ⟨hg.1, fun hall => hg.2 (hpoint g hall)⟩
  have hden : 0 ≤ eventMass (RegularGraph.weight (N := N) (d := d))
      (RegularGraph.structural (logarithmicRadius (c / 4) d N) ω ⌊(N : ℝ) ^ c⌋₊) := by
    unfold eventMass
    exact Finset.sum_nonneg (fun g _ => by split_ifs <;> first | exact RegularGraph.weight_nonnegative g | positivity)
  exact (div_le_div_of_nonneg_right hmono hden).trans (hnat hnonempty)

end LocalLaw
