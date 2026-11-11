import LocalLaw.SourceClosureInputs
import LocalLaw.IndependentRadiusEvents
import LocalLaw.EffectiveModelRadius

/-!
# Actual Green, exceptional cavity and closure caps with independent radii

The weak model approximation uses the effective internal radius. Every paper
error, scalar prior, depth and sparse absorption budget retains the nominal
radius. All Green/pivot and exceptional-cavity caps are derived from the
actual weak split-radius event; no nominal weak event is inferred.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance independentRadiusSourceCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace RegularGraph
theorem eventually_sourceOmegaWithRadii_green_caps (a b d : ℕ) (c β B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (z : ℂ) (badCount : ℕ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N) (logarithmicRadius (c / 4) d N)
        (finiteOmega d) badCount z →
      (∀ i j, ‖g.G z i j‖ ≤ sourceGreenEntryCap d) ∧
        (∀ i, ‖(g.G z i i)⁻¹‖ ≤ sourceGreenPivotCap d B) := by
  let C := finiteReferenceConstant d
  let K := pairSensitivityConstant d
  let W := C * (B + 2)
  have hC : 1 ≤ C := finiteReferenceConstant_ge_one d hd
  have hCp : 0 < C := by linarith
  have hBp : 0 < B + 2 := by linarith
  have hWp : 0 < W := mul_pos hCp hBp
  have hWtwo : 2 ≤ W := by
    have hh := mul_nonneg hCp.le hB
    dsimp only [W]
    nlinarith
  have hK : 0 ≤ K := pairSensitivityConstant_nonnegative d
  have hquarter : 0 < 1 / (4 * W) := by positivity
  have hquarter_one : 1 / (4 * W) ≤ 1 := (div_le_one (by positivity : 0 < 4 * W)).mpr (by linarith)
  have hfeedback := eventually_source_kernel_feedback a b d β 1 (2 * C)
    (coreConvolutionConstant (finiteOmega d)) ha hb hd hβ (by norm_num) (by positivity)
    (by unfold coreConvolutionConstant; positivity)
  have hperturb := eventually_source_radius_boundary_small a b d β K (1 / (4 * W))
    ha hb hd hβ hK hquarter
  filter_upwards [hfeedback, hperturb, eventually_paperError_small a b d β ha hb hd hβ,
    eventually_source_radius_hierarchy a d c β hd hc hβ hβc,
    eventually_log_ge_nat 1, eventually_log_ge_nat (4 * W), Filter.eventually_ge_atTop 1]
    with N hfeedback hperturb herror hradii hlog hlogW hN
  intro g z badCount hz hzB hscale hOmega
  let r := effectiveModelRadius a d N β
  let R := logarithmicRadius (c / 4) d N
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let Ψ := scalarScale (spectralScale z) ε
  have hε : 0 ≤ ε := graphPaperError_nonnegative a d N (logarithmicRadius β d N) z hN hz.le
  have hΨ : 0 ≤ Ψ := scalarScale_nonneg hε
  have hprior : ‖g.Q z - semicircleRoot z‖ ≤ Ψ := hOmega.2.1
  have hballs : ∀ v, graphBallExcess g.graph v R ≤ finiteOmega d := hOmega.1.1
  have hrNom : r ≤ logarithmicRadius β d N := Nat.sub_le _ _
  have hmargin : 4 * r + 1 ≤ R := by
    have he := hradii.1
    have hl := hradii.2.1
    dsimp only [r, R]
    omega
  have hsmall : ‖g.Q z - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * (4 * (r : ℝ) + 2) ≤ 1 / 2 := by
    have hh := hfeedback z (g.Q z) hz hscale (by simpa only [one_mul] using hprior)
    have hfac : 0 ≤ ‖g.Q z - semicircleRoot z‖ * C * coreConvolutionConstant (finiteOmega d) := by
      have hCo := coreConvolutionConstant_nonnegative (finiteOmega d)
      positivity
    have hrCast : (r : ℝ) ≤ (logarithmicRadius β d N : ℝ) := by exact_mod_cast hrNom
    have hD := mul_le_mul_of_nonneg_left (show 4 * (r : ℝ) + 2 ≤
      2 * ((logarithmicRadius β d N : ℝ) * 2 + 1) by nlinarith only [hrCast]) hfac
    apply hD.trans
    convert hh using 1
    dsimp only [C]
    ring
  have hδ : K * ‖g.Q z - semicircleRoot z‖ ≤ 1 / (4 * W) := by
    have hh := hperturb z hz hscale
    change K * ((logarithmicRadius β d N : ℝ) + 1) * Ψ ≤ 1 / (4 * W) at hh
    have hp := mul_le_mul_of_nonneg_left hprior hK
    have hr : (0 : ℝ) ≤ logarithmicRadius β d N := Nat.cast_nonneg _
    nlinarith [mul_nonneg hK hΨ]
  have hεquarter : ε ≤ 1 / (4 * W) := by
    have hp : Real.log (N : ℝ) ≤ Real.log (N : ℝ) ^ (4 * a) := by
      simpa only [pow_one] using pow_le_pow_right₀ hlog (show 1 ≤ 4 * a by omega)
    have hlogp : 0 < Real.log (N : ℝ) := by linarith
    have he : ε ≤ (Real.log (N : ℝ) ^ (4 * a))⁻¹ := herror z hz hscale
    apply (he.trans (inv_anti₀ hlogp hp)).trans
    simpa only [one_div] using inv_anti₀ (show 0 < 4 * W by positivity) hlogW
  have hdiag : ε + K * ‖g.Q z - semicircleRoot z‖ ≤ 1 / (2 * C * (B + 2)) := by
    apply (add_le_add hεquarter hδ).trans_eq
    dsimp only [W]
    field_simp [ne_of_gt hCp, ne_of_gt hBp]
    ring
  exact g.green_caps_of_pair_approximation hd r R hmargin hballs z (g.Q z) hz
    (g.Q_im_nonnegative z hz) B ε hzB hOmega.2.2 (hεquarter.trans hquarter_one)
    (hδ.trans hquarter_one) hdiag hsmall


theorem eventually_sourceOmegaWithRadii_exceptional_cavity_cap (a b d : ℕ) (c β B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (z : ℂ) (badCount : ℕ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N) (logarithmicRadius (c / 4) d N)
        (finiteOmega d) badCount z →
      ∀ i, ‖cavityAtVertex g.graph d z i - cavityIterate z (g.Q z) (actualCavityDepth a d N z)‖ ≤
        sourceExceptionalCavityCap d B := by
  filter_upwards [eventually_sourceOmegaWithRadii_green_caps a b d c β B ha hb hd hc hβ hβc hB,
    eventually_actual_cavity_parameters a b d β ha hb hd hβ,
    eventually_paperError_small a b d β ha hb hd hβ,
    eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1] with N hcaps hparameters herror hlog hN
  intro g z badCount hz hzB hscale hOmega i
  have hG := hcaps g z badCount hz hzB hscale hOmega
  have hC : 0 ≤ sourceGreenEntryCap d := by
    have hh := finiteReferenceConstant_ge_one d hd
    unfold sourceGreenEntryCap
    linarith
  have hL : 0 ≤ sourceGreenPivotCap d B := by
    have hh := finiteReferenceConstant_ge_one d hd
    unfold sourceGreenPivotCap
    positivity
  have hcv := g.cavityAtVertex_norm_le_caps (by omega) z hz _ _ hC hL hG.1 hG.2 i
  have hprior : ‖g.Q z - semicircleRoot z‖ ≤ scalarScale (spectralScale z)
      (graphPaperError a d N (logarithmicRadius β d N) z) := hOmega.2.1
  have he := herror z hz hscale
  have hε : 0 ≤ graphPaperError a d N (logarithmicRadius β d N) z :=
    graphPaperError_nonnegative _ _ _ _ _ hN hz.le
  have hlogp : 0 < Real.log (N : ℝ) := by linarith
  have hεone : graphPaperError a d N (logarithmicRadius β d N) z ≤ 1 :=
    he.trans ((inv_le_one₀ (pow_pos hlogp _)).mpr (one_le_pow₀ hlog))
  have hscaleone : scalarScale (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z) ≤ 1 :=
    (scalarScale_le_sqrt (spectralScale_pos hz) hε).trans
      (Real.sqrt_le_iff.mpr ⟨by norm_num, by simpa using hεone⟩)
  have hsmall := (hparameters z hz hscale).2.2.2
  have hsmall' : (actualCavityDepth a d N z : ℝ) * ‖g.Q z - semicircleRoot z‖ ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hprior (Nat.cast_nonneg _)).trans hsmall
  have hiter := cavity_iterate_norm_le_three (semicircleRoot z) z (g.Q z) _
    (semicircleRoot_equation z) (semicircleRoot_norm_le_one z) hsmall' (hprior.trans hscaleone)
  exact (norm_sub_le _ _).trans (by
    change ‖cavityAtVertex g.graph d z i‖ + ‖cavityIterate z (g.Q z) (actualCavityDepth a d N z)‖ ≤
      (sourceGreenEntryCap d + sourceGreenEntryCap d ^ 2 * sourceGreenPivotCap d B) + 3
    linarith)


end RegularGraph

theorem eventually_source_closure_inputs_with_radii (a b d : ℕ) (c β γ B U V : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hγβ : γ + β ≤ 1)
    (hB : 0 ≤ B) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ, 0 < z.im → ‖z‖ ≤ B →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∃ D : ClosureBudget z (semicircleRoot z) (spectralScale z)
          (graphPaperError a d N (logarithmicRadius β d N) z),
        D.depth = actualCavityDepth a d N z ∧ D.L = Real.log (N : ℝ) ∧
        D.rowBase = U * graphPaperError a d N (logarithmicRadius β d N) z / Real.log (N : ℝ) ∧
        D.rowFeedback = V * Real.log (N : ℝ) ∧
        D.cavityError = graphPaperError a d N (logarithmicRadius β d N) z /
          (2 * Real.log (N : ℝ) ^ 2) ∧ D.exceptionalCavity = sourceExceptionalCavityCap d B ∧
        ∀ g : RegularGraph N d,
          RegularGraph.offsetStructural (logarithmicRadius (c / 4) d N) (finiteOmega d) 1 ⌊(N : ℝ) ^ γ⌋₊ g →
          (graphLocalLawFamilyWithRadii N d a (effectiveModelRadius a d N β) (logarithmicRadius β d N)).weak z g →
          (∀ i ∈ nonTreeCenters g.graph (logarithmicRadius (c / 4) d N),
            ‖cavityAtVertex g.graph d z i - cavityIterate z (g.Q z) D.depth‖ ≤ D.exceptionalCavity) ∧
          D.cavityError + (((nonTreeCenters g.graph (logarithmicRadius (c / 4) d N)).card : ℝ) / (N : ℝ)) *
              D.exceptionalCavity ≤ graphPaperError a d N (logarithmicRadius β d N) z / D.L ^ 2 := by
  let M := sourceExceptionalCavityCap d B
  have hM : 0 ≤ M := sourceExceptionalCavityCap_nonnegative d hd B hB
  filter_upwards [eventually_actual_closure_budget a b d β B U V M ha hb hd hβ hU hV,
    RegularGraph.eventually_sourceOmegaWithRadii_exceptional_cavity_cap a b d c β B ha hb hd hc hβ hβc hB,
    eventually_sparse_cavity_absorption a d β γ M (by omega) hd hβ.le hγβ hM]
    with N hbudget hcaps habsorb
  intro z hz hzB hscale
  obtain ⟨D, hdepth, hlog, hrow, hfeedback, hcavity, hexceptional⟩ := hbudget z hz hscale hzB
  refine ⟨D, hdepth, hlog, hrow, hfeedback, hcavity, hexceptional, ?_⟩
  intro g haux hweak
  have hstruct := RegularGraph.offsetStructural_implies_structural haux
  have hOmega : g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N) (logarithmicRadius (c / 4) d N)
      (finiteOmega d) ⌊(N : ℝ) ^ γ⌋₊ z := ⟨hstruct, hweak⟩
  have hbad : ((nonTreeCenters g.graph (logarithmicRadius (c / 4) d N)).card : ℝ) ≤ (N : ℝ) ^ γ :=
    (Nat.cast_le.mpr hstruct.2).trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) γ))
  constructor
  · intro i _
    rw [hdepth, hexceptional]
    exact hcaps g z _ hz hzB hscale hOmega i
  · rw [hcavity, hexceptional, hlog]
    have hs := habsorb _ hbad z hz.le
    calc
      _ ≤ graphPaperError a d N (logarithmicRadius β d N) z / (2 * Real.log (N : ℝ) ^ 2) +
          graphPaperError a d N (logarithmicRadius β d N) z / (2 * Real.log (N : ℝ) ^ 2) :=
        add_le_add_left hs _
      _ = _ := by ring


end LocalLaw
