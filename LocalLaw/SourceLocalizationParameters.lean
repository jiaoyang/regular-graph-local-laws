import LocalLaw.ComponentWeakLocalization
import LocalLaw.LocalizationErrorBounds
import LocalLaw.ParameterSmallness
import LocalLaw.ClosureParameters

/-!
# Realized source parameters for finite localization

The selected resampling depth and actual integer logarithmic radius have
proved logarithmic model-diameter caps. The actual paper error realizes the
scaled smallness and pays for the two-sided kernel tail, uniformly on the
source spectral domain. Thus no finite localization budget is left as a
source hypothesis.
-/

open Filter
noncomputable section
namespace LocalLaw

def sourceLocalizationLogCap (d : ℕ) (β : ℝ) : ℝ :=
  (2 * (finiteOmega d : ℝ) + 12) * (1 + β / Real.log ((d - 1 : ℕ) : ℝ))

theorem sourceLocalizationLogCap_nonnegative (d : ℕ) (hd : 3 ≤ d) (β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ sourceLocalizationLogCap d β := by
  have hk : 1 < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < d - 1 by omega)
  unfold sourceLocalizationLogCap
  exact mul_nonneg (by positivity) (add_nonneg (by norm_num) (div_nonneg hβ (Real.log_pos hk).le))

private theorem logarithmic_model_caps (n ell r : ℕ) (L θ : ℝ) (hL : 1 ≤ L) (hθ : 0 ≤ θ)
    (hell : (ell : ℝ) ≤ L) (hr : (r : ℝ) ≤ θ * L) :
    ((((6 * (ell + r) + 2 : ℕ) + 1 : ℝ) ≤ (2 * (n : ℝ) + 12) * (1 + θ) * L) ∧
      (((2 * r + (n + 2) * (2 * r + 1) : ℕ) + 1 : ℝ) ≤ (2 * (n : ℝ) + 12) * (1 + θ) * L) ∧
      (((4 * r + 1 : ℕ) + 1 : ℝ) ≤ (2 * (n : ℝ) + 12) * (1 + θ) * L)) := by
  have hL0 : 0 ≤ L := by linarith
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hθL : 0 ≤ θ * L := mul_nonneg hθ hL0
  have h9 := mul_le_mul_of_nonneg_right (show 9 ≤ 2 * (n : ℝ) + 12 by linarith) hL0
  have h6 := mul_le_mul_of_nonneg_right (show 6 ≤ 2 * (n : ℝ) + 12 by linarith) hθL
  have hfull : ((6 * (ell + r) + 2 : ℕ) + 1 : ℝ) ≤ (2 * (n : ℝ) + 12) * (1 + θ) * L := by
    push_cast
    nlinarith only [hell, hr, hL, h9, h6]
  have hr' := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 * (n : ℝ) + 6 by linarith)
  have hW := mul_le_mul_of_nonneg_right hL (show 0 ≤ (n : ℝ) + 3 by positivity)
  have hV := mul_le_mul_of_nonneg_right (show 2 * (n : ℝ) + 6 ≤ 2 * (n : ℝ) + 12 by linarith) hθL
  have hU := mul_le_mul_of_nonneg_right (show (n : ℝ) + 3 ≤ 2 * (n : ℝ) + 12 by linarith) hL0
  refine ⟨hfull, ?_, ?_⟩
  · push_cast
    nlinarith only [hr', hW, hV, hU]
  · have hp : (4 * r + 1 : ℕ) + 1 ≤ (6 * (ell + r) + 2 : ℕ) + 1 := by omega
    have hpR : (((4 * r + 1 : ℕ) + 1 : ℝ)) ≤ (((6 * (ell + r) + 2 : ℕ) + 1 : ℝ)) := by exact_mod_cast hp
    exact hpR.trans hfull

structure SourceLocalizationBounds (a d N : ℕ) (β B : ℝ) (z : ℂ) : Prop where
  log_one : 1 ≤ Real.log (N : ℝ)
  error_nonnegative : 0 ≤ graphPaperError a d N (logarithmicRadius β d N) z
  error_scaled : graphPaperError a d N (logarithmicRadius β d N) z * Real.log (N : ℝ) ^ 4 ≤ 1
  large_log : DeficientGraph.localizationBudgetConstant d B (sourceLocalizationLogCap d β) ≤ Real.log (N : ℝ)
  full_cap : (((6 * ((actualCavityDepth a d N z - 1) + logarithmicRadius β d N) + 2 : ℕ) + 1 : ℝ)) ≤
    sourceLocalizationLogCap d β * Real.log (N : ℝ)
  deleted_cap : (((2 * logarithmicRadius β d N + (finiteOmega d + 2) *
    (2 * logarithmicRadius β d N + 1) : ℕ) + 1 : ℝ)) ≤ sourceLocalizationLogCap d β * Real.log (N : ℝ)
  pair_cap : (((4 * logarithmicRadius β d N + 1 : ℕ) + 1 : ℝ)) ≤
    sourceLocalizationLogCap d β * Real.log (N : ℝ)
  tail : physicalTransfer d z ^ (2 * logarithmicRadius β d N) ≤
    graphPaperError a d N (logarithmicRadius β d N) z

/-- Every numerical localization field follows for the actual selected
source parameters, uniformly for all spectral points above the source floor. -/
theorem eventually_sourceLocalizationBounds (a b d : ℕ) (β B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      SourceLocalizationBounds a d N β B z := by
  have hk : 1 < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < d - 1 by omega)
  have hlogk : 0 < Real.log ((d - 1 : ℕ) : ℝ) := Real.log_pos hk
  filter_upwards [eventually_paperError_small a b d β ha hb hd hβ,
    eventually_actualCavityDepth_le_log a d hd, eventually_log_ge_nat 1,
    eventually_log_ge_nat (DeficientGraph.localizationBudgetConstant d B (sourceLocalizationLogCap d β)),
    eventually_ge_atTop 1] with N hsmall hdepth hlog hlarge hN
  intro z hz hfloor
  let L := Real.log (N : ℝ)
  let r := logarithmicRadius β d N
  let ell := actualCavityDepth a d N z - 1
  let ε := graphPaperError a d N r z
  have hε : 0 ≤ ε := graphPaperError_nonnegative a d N r z hN hz.le
  have hsmallz := hsmall z hz hfloor
  change ε ≤ (L ^ (4 * a))⁻¹ at hsmallz
  have hLpos : 0 < L := by linarith
  have hscale : ε * L ^ (4 * a) ≤ 1 := by
    exact (le_div_iff₀ (pow_pos hLpos _)).mp (by simpa only [one_div] using hsmallz)
  have hpow : L ^ 4 ≤ L ^ (4 * a) := pow_le_pow_right₀ hlog (by omega)
  have hscaled : ε * L ^ 4 ≤ 1 := (mul_le_mul_of_nonneg_left hpow hε).trans hscale
  have hell : (ell : ℝ) ≤ L := (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (hdepth z)
  have hr : (r : ℝ) ≤ (β / Real.log ((d - 1 : ℕ) : ℝ)) * L := by
    have hh := Nat.floor_le (div_nonneg (mul_nonneg hβ.le hLpos.le) hlogk.le)
    change (logarithmicRadius β d N : ℝ) ≤ β * L / Real.log ((d - 1 : ℕ) : ℝ) at hh
    exact hh.trans_eq (by ring)
  have hcaps := logarithmic_model_caps (finiteOmega d) ell r L
    (β / Real.log ((d - 1 : ℕ) : ℝ)) hlog (div_nonneg hβ.le hlogk.le) hell hr
  refine ⟨hlog, hε, hscaled, hlarge, ?_, ?_, ?_, graphPaperError_localization_tail a d N r hd z hlog hz.le⟩
  · exact hcaps.1
  · exact hcaps.2.1
  · exact hcaps.2.2

namespace SourceLocalizationBounds
variable {a d N : ℕ} {β B : ℝ} {z : ℂ}

/-- A literal full neighborhood model now needs only its actual component
budget and proved geometric diameter; all localization numerics are supplied. -/
theorem full_model {U : Type} [Fintype U] [DecidableEq U]
    (S : SourceLocalizationBounds a d N β B z) (hd : 3 ≤ d) (hβ : 0 ≤ β)
    (model : DeficientGraph U d) (hclass : model.ComponentFiniteReferenceBudget)
    (q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (hB : ‖z‖ ≤ B)
    (hprior : ‖q - semicircleRoot z‖ ≤ scalarScale (spectralScale z)
      (graphPaperError a d N (logarithmicRadius β d N) z))
    (hdiam : ∀ u v, model.graph.dist u v ≤ 6 * ((actualCavityDepth a d N z - 1) + logarithmicRadius β d N) + 2)
    (u v : U) :
    ‖model.extensionGreen q z u v - model.P (logarithmicRadius β d N) z q u v‖ ≤
      DeficientGraph.localizationWeakConstant d B (sourceLocalizationLogCap d β) * Real.log (N : ℝ) *
        graphPaperError a d N (logarithmicRadius β d N) z :=
  model.componentwise_weak_pair_localization hd hclass q z hz hq B hB _ _ _ S.error_nonnegative S.log_one
    (sourceLocalizationLogCap_nonnegative d hd β hβ) S.error_scaled hprior _ _ hdiam
    S.full_cap S.pair_cap S.large_log S.tail u v

/-- The actual deleted-neighborhood diameter receives the same realized
localization rate and the same degree/domain constant. -/
theorem deleted_model {U : Type} [Fintype U] [DecidableEq U]
    (S : SourceLocalizationBounds a d N β B z) (hd : 3 ≤ d) (hβ : 0 ≤ β)
    (model : DeficientGraph U d) (hclass : model.ComponentFiniteReferenceBudget)
    (q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (hB : ‖z‖ ≤ B)
    (hprior : ‖q - semicircleRoot z‖ ≤ scalarScale (spectralScale z)
      (graphPaperError a d N (logarithmicRadius β d N) z))
    (hdiam : ∀ u v, model.graph.dist u v ≤ 2 * logarithmicRadius β d N + (finiteOmega d + 2) *
      (2 * logarithmicRadius β d N + 1))
    (u v : U) :
    ‖model.extensionGreen q z u v - model.P (logarithmicRadius β d N) z q u v‖ ≤
      DeficientGraph.localizationWeakConstant d B (sourceLocalizationLogCap d β) * Real.log (N : ℝ) *
        graphPaperError a d N (logarithmicRadius β d N) z :=
  model.componentwise_weak_pair_localization hd hclass q z hz hq B hB _ _ _ S.error_nonnegative S.log_one
    (sourceLocalizationLogCap_nonnegative d hd β hβ) S.error_scaled hprior _ _ hdiam
    S.deleted_cap S.pair_cap S.large_log S.tail u v

end SourceLocalizationBounds
end LocalLaw
