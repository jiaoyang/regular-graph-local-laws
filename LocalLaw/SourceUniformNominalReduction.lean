import LocalLaw.SourceBoundedBootstrapReduction
import LocalLaw.EffectiveModelRate
import LocalLaw.ExteriorNominalRate
import LocalLaw.SourceLocalLawIdentifiers

/-! # The whole nominal spectral domain from the first-stage estimate

The continuum bootstrap covers modulus at most 2d. Genuine exterior
resolvent estimates cover the remaining unbounded domain. Both use the
same fixed degree-dependent entry and trace constant.
-/

namespace LocalLaw
noncomputable section
local instance sourceUniformNominalDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceUniformLawConstant (d : ℕ) : ℝ :=
  |sourceWidthConstant (2 * d) + pairSensitivityConstant d + 1| + 4

theorem sourceUniformLawConstant_ge_four (d : ℕ) : 4 ≤ sourceUniformLawConstant d := by
  unfold sourceUniformLawConstant
  linarith [abs_nonneg (sourceWidthConstant (2 * d) + pairSensitivityConstant d + 1)]

theorem eventually_source_uniform_nominal_of_first_stage (a b d p Cq : ℕ) (c β γ C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hp : 37 ≤ p)
    (hc : 0 < c) (hc₁ : c < 1) (hβ : 0 < β) (hβc : β ≤ c / 32)
    (hγ : c / 4 < γ) (hgap : γ + β < 1) (hC1 : 1 ≤ C1)
    (hCdel : sourceDeletionConstant d β (4 * d) ≤ C1) (hCq : finiteOmega d ≤ Cq)
    (hfirst : SourceFirstStageEstimate a b d p Cq c β γ (4 * d) C1) :
    ∀ᶠ N : ℕ in Filter.atTop,
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        RegularGraph.offsetStructural (logarithmicRadius (c / 4) d N) (finiteOmega d) 1 ⌊(N : ℝ) ^ γ⌋₊ g ∧
          ¬∀ z : ℂ, 0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
            ActualGraphLocalLawAt a (logarithmicRadius β d N) (sourceUniformLawConstant d)
              (sourceUniformLawConstant d) z g) ≤
        9 * bootstrapGridConstant (2 * d) / (N : ℝ) ^ (p - 37) := by
  have hwork : 2 * ((2 : ℝ) * d) = 4 * d := by ring
  have hfirst' : SourceFirstStageEstimate a b d p Cq c β γ (2 * (2 * d)) C1 := by simpa only [hwork] using hfirst
  have hCdel' : sourceDeletionConstant d β (2 * (2 * d)) ≤ C1 := by simpa only [hwork] using hCdel
  filter_upwards [eventually_source_bounded_weak_of_first_stage a b d p Cq c β γ (2 * d) C1
      ha hb hd hp hc hc₁ hβ hβc hγ hgap le_rfl hC1 hCdel' hCq hfirst',
    RegularGraph.eventually_actual_nominal_local_law_of_effective_weak a b d c β γ (2 * d)
      ha hb hd hc hβ hβc hgap.le (by positivity),
    RegularGraph.eventually_exterior_actual_nominal_local_law a b d β γ ha hb hd hβ hgap.le,
    eventually_source_radius_hierarchy a d c β hd hc hβ hβc, Filter.eventually_ge_atTop 1]
    with N hbounded htransfer hexterior hradii hN
  let R := logarithmicRadius (c / 4) d N
  let rn := logarithmicRadius β d N
  let r := effectiveModelRadius a d N β
  let A : RegularGraph N d → Prop := RegularGraph.offsetStructural R (finiteOmega d) 1 ⌊(N : ℝ) ^ γ⌋₊
  let F := graphLocalLawFamilyWithRadii N d a r rn
  let C := sourceUniformLawConstant d
  have hC4 : 4 ≤ C := sourceUniformLawConstant_ge_four d
  have hCb : sourceWidthConstant (2 * d) + pairSensitivityConstant d + 1 ≤ C := by
    dsimp only [C, sourceUniformLawConstant]
    linarith [le_abs_self (sourceWidthConstant (2 * d) + pairSensitivityConstant d + 1)]
  have hcover : ∀ g, A g → (∀ z ∈ boundedLocalLawDomain N b (2 * d), F.weak z g) →
      ∀ z : ℂ, 0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
        ActualGraphLocalLawAt a rn C C z g := by
    intro g hg hweak z hz hfloor
    by_cases hnorm : ‖z‖ ≤ 2 * d
    · exact (htransfer g z hz hnorm hfloor hg (hweak z ⟨hnorm, hfloor⟩)).mono_constants hN hz.le hCb hCb
    · have hstruct := RegularGraph.offsetStructural_implies_structural hg
      have hbad : ((nonTreeCenters g.graph R).card : ℝ) ≤ (N : ℝ) ^ γ :=
        (Nat.cast_le.mpr hstruct.2).trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) γ))
      have hR : rn ≤ R := by
        have hh := hradii.1
        dsimp only [rn, R]
        omega
      exact (hexterior g R hR hbad z hz (le_of_not_ge hnorm) hfloor).mono_constants hN hz.le (by linarith) hC4
  apply (eventMass_mono RegularGraph.weight RegularGraph.weight_nonnegative ?_).trans hbounded
  intro g hg
  exact ⟨hg.1, fun hw => hg.2 (hcover g hg.1 hw)⟩

end
end LocalLaw
