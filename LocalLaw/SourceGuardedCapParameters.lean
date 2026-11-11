import LocalLaw.SourceGuardedCaps
import LocalLaw.BoundaryPerturbationParameters

/-! # Realized scalar budgets for safe source Green caps

The actual nominal paper error makes both the full and deleted approximation
errors small. The source scalar prior controls boundary correction and all
base/extended feedback products uniformly for every shorter model radius.
No Green entry, pivot, or model estimate is supplied as an asymptotic input.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw

local instance sourceGuardedCapParametersDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem eventually_sourceLocalCapBounds (a b d : ℕ) (β C1 B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hβ : 0 < β)
    (hC1 : 0 ≤ C1) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ z q : ℂ, 0 < z.im →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ∀ r : ℕ,
      r ≤ logarithmicRadius β d N →
      ‖q - semicircleRoot z‖ ≤ C1 * scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      SourceLocalCapBounds d r z q B (C1 / Real.log (N : ℝ))
        (C1 * inflatedPrime (Real.log (N : ℝ)) (graphPaperError a d N (logarithmicRadius β d N) z)) ∧
      ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
        coreConvolutionConstant (finiteOmega d + 1) * (4 * (r : ℝ) + 2) ≤ 1 / 2 := by
  let C := finiteReferenceConstant d
  let K := pairSensitivityConstant d
  let W := C * (B + 2)
  have hC : 1 ≤ C := finiteReferenceConstant_ge_one d hd
  have hCp : 0 < C := by linarith
  have hK : 0 ≤ K := pairSensitivityConstant_nonnegative d
  have hW : 2 ≤ W := by dsimp only [W]; nlinarith [mul_nonneg hCp.le hB]
  have hWp : 0 < W := by linarith
  have hquarter : 0 < 1 / (4 * W) := by positivity
  have hquarterOne : 1 / (4 * W) ≤ 1 := (div_le_one (by positivity : 0 < 4 * W)).mpr (by linarith)
  have hbase := eventually_source_kernel_feedback a b d β C1 (2 * C)
    (coreConvolutionConstant (finiteOmega d)) ha hb hd hβ hC1 (by positivity)
    (coreConvolutionConstant_nonnegative _)
  have hextra := eventually_source_kernel_feedback a b d β C1 (2 * finiteExtraReferenceConstant d)
    (coreConvolutionConstant (finiteOmega d + 1)) ha hb hd hβ hC1
    (by have hh := finiteExtraReferenceConstant_ge_one d hd; positivity)
    (coreConvolutionConstant_nonnegative _)
  have hchange := eventually_source_radius_boundary_small a b d β (C1 * K) (1 / (4 * W))
    ha hb hd hβ (mul_nonneg hC1 hK) hquarter
  filter_upwards [hbase, hextra, hchange, eventually_paperError_small a b d β ha hb hd hβ,
    eventually_log_ge_nat 1, eventually_log_ge_nat (4 * W * C1), Filter.eventually_ge_atTop 1] with
      N hbase hextra hchange herror hL hlarge hN
  intro z q hz hscale r hr hprior
  let L := Real.log (N : ℝ)
  let rn := logarithmicRadius β d N
  let ε := graphPaperError a d N rn z
  let Ψ := scalarScale (spectralScale z) ε
  have hLp : 0 < L := by dsimp only [L]; linarith
  have hε : 0 ≤ ε := graphPaperError_nonnegative a d N rn z hN hz.le
  have hΨ : 0 ≤ Ψ := scalarScale_nonneg hε
  have hfull : C1 / L ≤ 1 / (4 * W) := by
    apply (div_le_div_iff₀ hLp (show 0 < 4 * W by positivity)).mpr
    dsimp only [L]
    nlinarith only [hlarge]
  have hεfour : ε * L ^ 4 ≤ 1 := by
    have hh : ε ≤ (L ^ (4 * a))⁻¹ := herror z hz hscale
    have hp : L ^ 4 ≤ L ^ (4 * a) := pow_le_pow_right₀ hL (by omega)
    calc
      _ ≤ (L ^ (4 * a))⁻¹ * L ^ 4 := mul_le_mul_of_nonneg_right hh (pow_nonneg hLp.le _)
      _ ≤ (L ^ (4 * a))⁻¹ * L ^ (4 * a) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt (pow_pos hLp _))
  have hdeleted : C1 * inflatedPrime L ε ≤ C1 / L := by
    apply (le_div_iff₀ hLp).mpr
    calc
      _ = C1 * (ε * L ^ 4) := by unfold inflatedPrime; ring
      _ ≤ C1 * 1 := mul_le_mul_of_nonneg_left hεfour hC1
      _ = C1 := mul_one _
  have hdelta : K * ‖q - semicircleRoot z‖ ≤ 1 / (4 * W) := by
    have hh := hchange z hz hscale
    change (C1 * K) * ((rn : ℝ) + 1) * Ψ ≤ 1 / (4 * W) at hh
    have hp := mul_le_mul_of_nonneg_left hprior hK
    have hrn : (0 : ℝ) ≤ rn := Nat.cast_nonneg _
    nlinarith [mul_nonneg (mul_nonneg hC1 hK) hΨ]
  have hsmall (F C₀ : ℝ) (hF : 0 ≤ F) (hC₀ : 0 ≤ C₀)
      (hh : ‖q - semicircleRoot z‖ * (2 * F) * C₀ * (2 * (rn : ℝ) + 1) ≤ 1 / 2) :
      ‖q - semicircleRoot z‖ * F * C₀ * (4 * (r : ℝ) + 2) ≤ 1 / 2 := by
    have hcast : (r : ℝ) ≤ rn := Nat.cast_le.mpr hr
    calc
      _ ≤ ‖q - semicircleRoot z‖ * F * C₀ * (2 * (2 * (rn : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ‖q - semicircleRoot z‖ * (2 * F) * C₀ * (2 * (rn : ℝ) + 1) := by ring
      _ ≤ 1 / 2 := hh
  have hpivot : C1 / L + K * ‖q - semicircleRoot z‖ ≤ 1 / (2 * C * (B + 2)) := by
    apply (add_le_add hfull hdelta).trans_eq
    dsimp only [W]
    field_simp [ne_of_gt hCp, show B + 2 ≠ 0 by positivity]
    ring
  refine ⟨⟨hsmall C _ hCp.le (coreConvolutionConstant_nonnegative _) (hbase z q hz hscale hprior),
    hdelta.trans hquarterOne, hfull.trans hquarterOne, hdeleted.trans (hfull.trans hquarterOne),
    hpivot, ?_⟩, ?_⟩
  · exact (add_le_add_right hdeleted _).trans hpivot
  · exact hsmall _ _ ((by norm_num : (0 : ℝ) ≤ 1).trans (finiteExtraReferenceConstant_ge_one d hd))
      (coreConvolutionConstant_nonnegative _) (hextra z q hz hscale hprior)

end LocalLaw
