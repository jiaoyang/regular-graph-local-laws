import LocalLaw.SourceFirstStageProof
import LocalLaw.SourceTheorem42Reduction

/-! # The actual uniform local law

All first- and second-stage resampling estimates are proved. The main theorem
uses the constructed positive reference threshold and has no analytic input.
The companion theorem permits any threshold in the literal finite-core infinite
extension class. Ensemble nonemptiness remains explicit.
-/
noncomputable section
namespace LocalLaw
local instance sourceTheorem42Decidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem source_theorem_4_2_of_reference_threshold (d ω : ℕ) (a b c β : ℝ)
    (hd : 3 ≤ d) (hω : 1 ≤ ω)
    (hreference : SourceFiniteCoreReferenceThreshold d ω (by omega))
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hc : 0 < c) (hc₁ : c < 1)
    (hβ : 0 < β) (hβc : β ≤ c / 32) :
    ∀ D : ℕ, ∀ᶠ N : ℕ in Filter.atTop, Nonempty (RegularGraph N d) →
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        RegularGraph.structural (logarithmicRadius (c / 4) d N) ω ⌊(N : ℝ) ^ c⌋₊ g ∧
          ¬∀ z : ℂ, 0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
            RealSourceLocalLawAt (by omega) a (logarithmicRadius β d N) (sourceUniformLawConstant d) z g) /
        eventMass (RegularGraph.weight (N := N) (d := d))
          (RegularGraph.structural (logarithmicRadius (c / 4) d N) ω ⌊(N : ℝ) ^ c⌋₊) ≤
        1 / (N : ℝ) ^ D := by
  have ha0:0≤a:=by linarith
  have hA:12≤⌊a⌋₊:=(Nat.le_floor_iff ha0).mpr ha
  apply source_theorem_4_2_of_first_stage d ω a b c β hd hω hreference ha hb hc hc₁ hβ hβc
  exact source_first_stage_all_powers ⌊a⌋₊ (25*⌊a⌋₊) d c β (7*c/8) (4*d)
    hA le_rfl hd hc hc₁ hβ hβc (by linarith) (by linarith) (by positivity)

theorem source_theorem_4_2 (d : ℕ) (a b c β : ℝ)
    (hd : 3 ≤ d)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hc : 0 < c) (hc₁ : c < 1)
    (hβ : 0 < β) (hβc : β ≤ c / 32) :
    ∀ D : ℕ, ∀ᶠ N : ℕ in Filter.atTop, Nonempty (RegularGraph N d) →
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        RegularGraph.structural (logarithmicRadius (c / 4) d N) (finiteOmega d) ⌊(N : ℝ) ^ c⌋₊ g ∧
          ¬∀ z : ℂ, 0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
            RealSourceLocalLawAt (by omega) a (logarithmicRadius β d N) (sourceUniformLawConstant d) z g) /
        eventMass (RegularGraph.weight (N := N) (d := d))
          (RegularGraph.structural (logarithmicRadius (c / 4) d N) (finiteOmega d) ⌊(N : ℝ) ^ c⌋₊) ≤
        1 / (N : ℝ) ^ D :=
  source_theorem_4_2_of_reference_threshold d (finiteOmega d) a b c β hd
    (finiteOmega_positive d hd) (finiteOmega_source_reference_good d hd)
    ha hb hc hc₁ hβ hβc

end LocalLaw
