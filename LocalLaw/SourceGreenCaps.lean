import LocalLaw.PairModelReferenceBounds
import LocalLaw.BoundaryPerturbationParameters
import LocalLaw.RadiusHierarchy

/-!
# Actual Green-entry and inverse-diagonal caps from the weak source event

The physical pair reference bounds are derived componentwise from structural
balls. A genuinely small approximation and boundary error then give finite
uniform Green and pivot caps. The large-N source wrapper supplies all the
numeric smallness conditions, retaining a bounded spectral domain explicitly.
-/

namespace LocalLaw
noncomputable section
local instance sourceCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

noncomputable def pairSensitivityConstant (d : ℕ) : ℝ :=
  8 * finiteReferenceConstant d ^ 2 * coreConvolutionConstant (finiteOmega d)

noncomputable def sourceGreenEntryCap (d : ℕ) : ℝ := finiteReferenceConstant d + 2
noncomputable def sourceGreenPivotCap (d : ℕ) (B : ℝ) : ℝ := 2 * finiteReferenceConstant d * (B + 2)

theorem pairSensitivityConstant_nonnegative (d : ℕ) : 0 ≤ pairSensitivityConstant d := by
  unfold pairSensitivityConstant coreConvolutionConstant
  positivity

namespace RegularGraph
variable {N d : ℕ}

/-- Actual full Green caps from an actual pair-model approximation. -/
theorem green_caps_of_pair_approximation (g : RegularGraph N d) (hd : 3 ≤ d) (r R : ℕ)
    (hmargin : 4 * r + 1 ≤ R) (hballs : ∀ a, graphBallExcess g.graph a R ≤ finiteOmega d)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (B E : ℝ) (hzB : ‖z‖ ≤ B)
    (happrox : ∀ i j, ‖g.G z i j - g.P r z q i j‖ ≤ E)
    (hE : E ≤ 1) (hchange : pairSensitivityConstant d * ‖q - semicircleRoot z‖ ≤ 1)
    (hdiagonal : E + pairSensitivityConstant d * ‖q - semicircleRoot z‖ ≤
      1 / (2 * finiteReferenceConstant d * (B + 2)))
    (small : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * (4 * (r : ℝ) + 2) ≤ 1 / 2) :
    (∀ i j, ‖g.G z i j‖ ≤ sourceGreenEntryCap d) ∧
      (∀ i, ‖(g.G z i i)⁻¹‖ ≤ sourceGreenPivotCap d B) := by
  have hC := finiteReferenceConstant_ge_one d hd
  have hB : 0 ≤ B := (norm_nonneg z).trans hzB
  have hW : 0 < finiteReferenceConstant d * (B + 2) := mul_pos (by linarith) (by linarith)
  constructor
  · intro i j
    have hmodel := g.pairP_perturbed_entry_bound hd r R hmargin hballs z q hz hq small i j
    have hsum := norm_add_le (g.P r z q i j) (g.G z i j - g.P r z q i j)
    rw [add_sub_cancel] at hsum
    change ‖g.G z i j‖ ≤ finiteReferenceConstant d + 2
    change ‖g.P r z q i j‖ ≤ finiteReferenceConstant d + pairSensitivityConstant d * ‖q - semicircleRoot z‖ at hmodel
    linarith [happrox i j]
  · intro i
    have href := (g.pairP_reference_diagonal_bounds hd r R hmargin hballs z hz B hzB i).1
    have hmodel := g.pairP_boundary_uniform_stability hd r R hmargin hballs z q hz hq small i i
    change ‖g.P r z q i i - g.P r z (semicircleRoot z) i i‖ ≤ pairSensitivityConstant d * ‖q - semicircleRoot z‖ at hmodel
    have hdist : ‖g.P r z (semicircleRoot z) i i - g.G z i i‖ ≤
        pairSensitivityConstant d * ‖q - semicircleRoot z‖ + E := by
      have hh := norm_add_le (g.P r z (semicircleRoot z) i i - g.P r z q i i)
        (g.P r z q i i - g.G z i i)
      rw [sub_add_sub_cancel] at hh
      apply hh.trans
      exact add_le_add (by simpa only [norm_sub_rev] using hmodel)
        (by simpa only [norm_sub_rev] using happrox i i)
    have hlower : 1 / (2 * finiteReferenceConstant d * (B + 2)) ≤ ‖g.G z i i‖ := by
      have hsplit : 1 / (finiteReferenceConstant d * (B + 2)) =
          2 * (1 / (2 * finiteReferenceConstant d * (B + 2))) := by field_simp; ring
      have hh := norm_sub_norm_le (g.P r z (semicircleRoot z) i i) (g.G z i i)
      linarith
    have hpositive : 0 < 1 / (2 * finiteReferenceConstant d * (B + 2)) := by positivity
    rw [norm_inv]
    calc
      _ ≤ (1 / (2 * finiteReferenceConstant d * (B + 2)))⁻¹ := inv_anti₀ hpositive hlower
      _ = sourceGreenPivotCap d B := by simp [sourceGreenPivotCap]

/-- Every large-N weak source event supplies actual Green-entry and inverse
pivot caps on a bounded spectral disk. No model-entry or diagonal estimate
is left as a hypothesis. -/
theorem eventually_sourceOmega_green_caps (a b d : ℕ) (c β B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (z : ℂ) (badCount : ℕ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      g.SourceOmega a (logarithmicRadius β d N) (logarithmicRadius (c / 4) d N)
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
  let r := logarithmicRadius β d N
  let R := logarithmicRadius (c / 4) d N
  let ε := graphPaperError a d N r z
  let Ψ := scalarScale (spectralScale z) ε
  have hε : 0 ≤ ε := graphPaperError_nonnegative a d N r z hN hz.le
  have hΨ : 0 ≤ Ψ := scalarScale_nonneg hε
  have hprior : ‖g.Q z - semicircleRoot z‖ ≤ Ψ := hOmega.2.1
  have hballs : ∀ v, graphBallExcess g.graph v R ≤ finiteOmega d := hOmega.1.1
  have hmargin : 4 * r + 1 ≤ R := by
    have he := hradii.1
    have hl := hradii.2.1
    dsimp only [r, R]
    omega
  have hsmall : ‖g.Q z - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * (4 * (r : ℝ) + 2) ≤ 1 / 2 := by
    have hh := hfeedback z (g.Q z) hz hscale (by simpa only [one_mul] using hprior)
    convert hh using 1
    dsimp only [C, r]
    ring
  have hδ : K * ‖g.Q z - semicircleRoot z‖ ≤ 1 / (4 * W) := by
    have hh := hperturb z hz hscale
    change K * ((r : ℝ) + 1) * Ψ ≤ 1 / (4 * W) at hh
    have hp := mul_le_mul_of_nonneg_left hprior hK
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
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

end RegularGraph
end
end LocalLaw
