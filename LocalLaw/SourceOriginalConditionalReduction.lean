import LocalLaw.SourceUniformNominalReduction
import LocalLaw.PolynomialFailureAbsorption

/-! # Recover the original structural conditioning and absorb probability constants

The bootstrap numerator uses the larger finite reference budget. The final
denominator is the original source event at omega. Its actual mass lower
bound is proved independently, and every auxiliary sparse-event loss is
charged before the final polynomial constant is absorbed.
-/

noncomputable section
namespace LocalLaw
local instance sourceOriginalConditionalDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem eventually_source_nominal_conditional_of_first_stage (a b d ω D : ℕ) (c β γ : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hω : 1 ≤ ω) (hωmax : ω ≤ finiteOmega d)
    (hc : 0 < c) (hc₁ : c < 1) (hβ : 0 < β) (hβc : β ≤ c / 32)
    (hγ : 3 * c / 4 < γ) (hgap : γ + β < 1)
    (hfirst : SourceFirstStageAllPowers a b d c β γ (4 * d)) :
    ∀ᶠ N : ℕ in Filter.atTop, Nonempty (RegularGraph N d) →
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        RegularGraph.structural (logarithmicRadius (c / 4) d N) ω ⌊(N : ℝ) ^ c⌋₊ g ∧
          ¬∀ z : ℂ, 0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
            ActualGraphLocalLawAt a (logarithmicRadius β d N) (sourceUniformLawConstant d)
              (sourceUniformLawConstant d) z g) /
        eventMass (RegularGraph.weight (N := N) (d := d))
          (RegularGraph.structural (logarithmicRadius (c / 4) d N) ω ⌊(N : ℝ) ^ c⌋₊) ≤
        1 / (N : ℝ) ^ D := by
  obtain ⟨Cq, C1, hCq, hC1, hCdel, hstage⟩ := hfirst (D + 39)
  have hgrid : 0 ≤ bootstrapGridConstant (2 * d) := by unfold bootstrapGridConstant; positivity
  filter_upwards [eventually_source_uniform_nominal_of_first_stage a b d (D + 39) Cq c β γ C1
      ha hb hd (by omega) hc hc₁ hβ hβc (by linarith) hgap hC1 hCdel hCq hstage,
    eventually_offset_original_failure_transfer d ω 1 (D + 1) c γ hd hω hc hc₁ hγ,
    eventually_const_div_pow_succ_le (2 + 18 * bootstrapGridConstant (2 * d)) D,
    Filter.eventually_ge_atTop 1] with N huniform htransfer habsorb hN
  intro hnonempty
  let R := logarithmicRadius (c / 4) d N
  let badCount := ⌊(N : ℝ) ^ γ⌋₊
  let failure : RegularGraph N d → Prop := fun g =>
    ¬∀ z : ℂ, 0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ActualGraphLocalLawAt a (logarithmicRadius β d N) (sourceUniformLawConstant d)
        (sourceUniformLawConstant d) z g
  have hnum : eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
      RegularGraph.offsetStructural R (finiteOmega d) 1 badCount g ∧ failure g) ≤
        9 * bootstrapGridConstant (2 * d) / (N : ℝ) ^ (D + 2) := by
    simpa only [show D + 39 - 37 = D + 2 by omega] using huniform
  have hinside : eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
      RegularGraph.offsetStructural R ω 1 badCount g ∧ failure g) ≤
        9 * bootstrapGridConstant (2 * d) / (N : ℝ) ^ (D + 2) := by
    apply (eventMass_mono RegularGraph.weight RegularGraph.weight_nonnegative ?_).trans hnum
    intro g hg
    exact ⟨⟨fun o => (hg.1.1 o).trans hωmax, hg.1.2⟩, hg.2⟩
  have hconditional := htransfer hnonempty failure
    (9 * bootstrapGridConstant (2 * d) / (N : ℝ) ^ (D + 2)) (by positivity) hinside
  apply hconditional.trans
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hstep : (18 * bootstrapGridConstant (2 * d)) / (N : ℝ) ^ (D + 2) ≤
      (18 * bootstrapGridConstant (2 * d)) / (N : ℝ) ^ (D + 1) :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos hNp _)
      (pow_le_pow_right₀ hNr (by omega))
  calc
    _ = 2 / (N : ℝ) ^ (D + 1) + (18 * bootstrapGridConstant (2 * d)) / (N : ℝ) ^ (D + 2) := by ring
    _ ≤ 2 / (N : ℝ) ^ (D + 1) + (18 * bootstrapGridConstant (2 * d)) / (N : ℝ) ^ (D + 1) :=
      add_le_add_left hstep _
    _ = (2 + 18 * bootstrapGridConstant (2 * d)) / (N : ℝ) ^ (D + 1) := by ring
    _ ≤ _ := habsorb

end LocalLaw
