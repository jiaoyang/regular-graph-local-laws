import LocalLaw.SourceModelTransfer
import LocalLaw.IndependentRadiusEvents
import LocalLaw.ReferenceRadiusComparison

/-!
# Actual entry/trace transfer at an independent internal model radius

The finite reference replacement and averaging argument keeps every scalar
paper budget at its nominal error radius. Only the physical model radius is
shortened; all model and diagonal bounds are still derived from actual balls.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance independentRadiusModelTransferDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def ActualGraphLocalLawWithRadiiAt {N d : ℕ} (a rModel rError : ℕ) (Centry Ctrace : ℝ)
    (z : ℂ) (g : RegularGraph N d) : Prop :=
  (∀ i j, ‖g.G z i j - g.P rModel z (semicircleRoot z) i j‖ ≤
    Centry * scalarScale (spectralScale z) (graphPaperError a d N rError z)) ∧
  ‖empiricalTransform g.H z - graphKestenMcKayReference d z‖ ≤
    Ctrace * scalarScale (spectralScale z) (graphPaperError a d N rError z)

@[simp] theorem ActualGraphLocalLawWithRadiiAt_diagonal {N d : ℕ}
    (a r : ℕ) (Centry Ctrace : ℝ) (z : ℂ) (g : RegularGraph N d) :
    ActualGraphLocalLawWithRadiiAt a r r Centry Ctrace z g ↔
      ActualGraphLocalLawAt a r Centry Ctrace z g := Iff.rfl

namespace RegularGraph
variable {N d : ℕ}
theorem actual_local_law_with_radii_of_weak_and_sparse (g : RegularGraph N d) (hd : 3 ≤ d)
    (a rModel rError R : ℕ) (hN : 0 < N) (hmargin : 4 * rModel + 1 ≤ R)
    (hballs : ∀ v, graphBallExcess g.graph v R ≤ finiteOmega d)
    (z : ℂ) (hz : 0 < z.im) (B : ℝ) (hzB : ‖z‖ ≤ B)
    (hweak : (graphLocalLawFamilyWithRadii N d a rModel rError).weak z g)
    (hε : graphPaperError a d N rError z ≤ 1)
    (small : ‖g.Q z - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * (4 * (rModel : ℝ) + 2) ≤ 1 / 2)
    (sparse : (((nonTreeCenters g.graph rModel).card : ℝ) / (N : ℝ)) *
      (finiteReferenceConstant d + 2) ≤
        scalarScale (spectralScale z) (graphPaperError a d N rError z)) :
    ActualGraphLocalLawWithRadiiAt a rModel rError (sourceWidthConstant B + pairSensitivityConstant d)
      (sourceWidthConstant B + pairSensitivityConstant d + 1) z g := by
  let ε := graphPaperError a d N rError z
  let Ψ := scalarScale (spectralScale z) ε
  have hεnonneg : 0 ≤ ε := graphPaperError_nonnegative a d N rError z (by omega) hz.le
  have hΨ : 0 ≤ Ψ := scalarScale_nonneg hεnonneg
  have hroot : 0 < Real.sqrt (spectralScale z + ε) :=
    Real.sqrt_pos.mpr (by linarith [spectralScale_pos hz])
  have hidentity : ε = Ψ * Real.sqrt (spectralScale z + ε) := by
    dsimp only [Ψ, scalarScale]
    field_simp
  have hwidth := source_bounded_width B z ε hzB hε
  have heps : ε ≤ sourceWidthConstant B * Ψ := by
    rw [hidentity]
    exact (mul_le_mul_of_nonneg_left hwidth hΨ).trans_eq (mul_comm _ _)
  have hsensitivity : ∀ i j, ‖g.P rModel z (g.Q z) i j - g.P rModel z (semicircleRoot z) i j‖ ≤
      pairSensitivityConstant d * dist (g.Q z) (semicircleRoot z) := by
    intro i j
    simpa only [Complex.dist_eq, pairSensitivityConstant] using
      g.pairP_boundary_uniform_stability hd rModel R hmargin hballs z (g.Q z) hz
        (g.Q_im_nonnegative z hz) small i j
  have hlocal := boundary_entry_trace (g.G z) (g.P rModel z) (g.Q z) (semicircleRoot z)
    (graphKestenMcKayReference d z) (nonTreeCenters g.graph rModel) ε Ψ
    (pairSensitivityConstant d) (finiteReferenceConstant d + 2)
    (pairSensitivityConstant_nonnegative d) (by simpa only [Fintype.card_fin] using hN)
    hweak.2 (by simpa only [Complex.dist_eq] using hweak.1)
    hsensitivity
    (fun i hi => g.pairP_diagonal_eq_reference_of_good hd rModel z hz i hi)
    (fun i _ => g.pairP_diagonal_reference_error hd rModel R hmargin hballs z hz i)
  constructor
  · intro i j
    exact (hlocal.1 i j).trans (by nlinarith)
  · rw [regularGraph_transform_sub_eq_average g z (graphKestenMcKayReference d z) hN]
    have hh := hlocal.2
    simp only [Fintype.card_fin] at hh
    exact hh.trans (by nlinarith)


theorem eventually_actual_local_law_with_radii_of_source_weak (a b d : ℕ) (c β γ B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hγβ : γ + β ≤ 1) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (rModel : ℕ), rModel ≤ logarithmicRadius β d N → ∀ (g : RegularGraph N d) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      offsetStructural (logarithmicRadius (c / 4) d N) (finiteOmega d) 1 ⌊(N : ℝ) ^ γ⌋₊ g →
      (graphLocalLawFamilyWithRadii N d a rModel (logarithmicRadius β d N)).weak z g →
      ActualGraphLocalLawWithRadiiAt a rModel (logarithmicRadius β d N)
        (sourceWidthConstant B + pairSensitivityConstant d)
        (sourceWidthConstant B + pairSensitivityConstant d + 1) z g := by
  let A := sourceWidthConstant B
  let M := finiteReferenceConstant d + 2
  have hA : 0 < A := sourceWidthConstant_pos B hB
  have hM : 0 ≤ M := by dsimp only [M]; linarith [finiteReferenceConstant_ge_one d hd]
  filter_upwards [eventually_source_kernel_feedback a b d β 1
      (2 * finiteReferenceConstant d) (coreConvolutionConstant (finiteOmega d)) ha hb hd hβ
      (by norm_num) (by linarith [finiteReferenceConstant_ge_one d hd])
      (by unfold coreConvolutionConstant; positivity),
    eventually_source_radius_hierarchy a d c β hd hc hβ hβc,
    eventually_paperError_small a b d β ha hb hd hβ,
    eventually_log_ge_nat 1, eventually_log_ge_nat (A * M),
    Filter.eventually_ge_atTop 1] with N hfeedback hradii herror hlog hconstant hN
  intro rModel hModel g z hz hzB hscale haux hweak
  let r := logarithmicRadius β d N
  let R := logarithmicRadius (c / 4) d N
  let ε := graphPaperError a d N r z
  let Ψ := scalarScale (spectralScale z) ε
  have hstruct := offsetStructural_implies_structural haux
  have hmargin : 4 * r + 1 ≤ R := by
    have hlarge := hradii.2.1
    have he := hradii.1
    dsimp only [r, R]
    omega
  have hmarginModel : 4 * rModel + 1 ≤ R := by change rModel ≤ r at hModel; omega
  have hrR : rModel ≤ R := by omega
  have hεnonneg : 0 ≤ ε := graphPaperError_nonnegative a d N r z hN hz.le
  have hsmallNom : ‖g.Q z - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * (4 * (r : ℝ) + 2) ≤ 1 / 2 := by
    have hh := hfeedback z (g.Q z) hz hscale (by simpa only [one_mul] using hweak.1)
    convert hh using 1
    dsimp only [r]
    ring
  have hsmall : ‖g.Q z - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * (4 * (rModel : ℝ) + 2) ≤ 1 / 2 := by
    apply le_trans _ hsmallNom
    apply mul_le_mul_of_nonneg_left
    · have hh : (rModel : ℝ) ≤ r := Nat.cast_le.mpr hModel
      linarith
    · have hcpos : 0 ≤ finiteReferenceConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans
        (finiteReferenceConstant_ge_one d hd)
      exact mul_nonneg (mul_nonneg (norm_nonneg _) hcpos) (by unfold coreConvolutionConstant; positivity)
  have hεone : ε ≤ 1 := by
    apply (herror z hz hscale).trans
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hlog)
  have hbad : ((nonTreeCenters g.graph rModel).card : ℝ) ≤ (N : ℝ) ^ γ := by
    apply (Nat.cast_le.mpr (Finset.card_le_card (nonTreeCenters_mono g.graph hrR))).trans
    exact (Nat.cast_le.mpr hstruct.2).trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) γ))
  have hwidth : Real.sqrt (spectralScale z + ε) ≤ A := source_bounded_width B z ε hzB hεone
  have hidentity : ε = Ψ * Real.sqrt (spectralScale z + ε) := by
    have hroot : 0 < Real.sqrt (spectralScale z + ε) :=
      Real.sqrt_pos.mpr (by linarith [spectralScale_pos hz])
    dsimp only [Ψ, scalarScale]
    field_simp
  have hsparse : (((nonTreeCenters g.graph rModel).card : ℝ) / (N : ℝ)) * M ≤ Ψ := by
    have hh := sparse_error_log_absorption N d a 0 β γ A M
      (nonTreeCenters g.graph rModel).card hN hd hβ.le hγβ hbad hA hM hlog (by omega) hconstant z hz.le
    simp only [pow_zero, mul_one] at hh
    apply hh.trans
    apply (div_le_iff₀ hA).mpr
    change ε ≤ Ψ * A
    rw [hidentity]
    exact mul_le_mul_of_nonneg_left hwidth (scalarScale_nonneg hεnonneg)
  exact g.actual_local_law_with_radii_of_weak_and_sparse hd a rModel r R (by omega) hmarginModel hstruct.1 z hz B hzB
    hweak hεone hsmall hsparse

end RegularGraph
end LocalLaw
