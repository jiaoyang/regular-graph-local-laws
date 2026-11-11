import LocalLaw.SourceLocalizationParameters
import LocalLaw.NeighborhoodPairIdentities
import LocalLaw.ComponentDeletionBudget
import LocalLaw.SharpSamplingCounts
import LocalLaw.RadiusHierarchy

/-!
# Realized source budgets for the deletion comparison

The actual removed ball has polylogarithmic size. Its cardinality times the
actual localization error is absorbed by the proved paper error cap, rather
than assumed as a Schur-complement smallness input.
-/

open Filter
noncomputable section
namespace LocalLaw
local instance sourceDeletionParametersDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace DeficientGraph

theorem localizationWeakConstant_ge_one (d : ℕ) (hd : 3 ≤ d) (B A : ℝ) (hA : 0 ≤ A) :
    1 ≤ localizationWeakConstant d B A := by
  have hC : 0 ≤ finiteExtraReferenceConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans
    (finiteExtraReferenceConstant_ge_one d hd)
  have hC0 := coreConvolutionConstant_nonnegative (finiteOmega d + 1)
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hk : 0 < (d : ℝ) - 1 := by linarith
  have hM : 0 ≤ localizationExceptionalMass d (2 : ℂ) := by
    unfold localizationExceptionalMass
    positivity
  unfold localizationWeakConstant
  dsimp only
  have h1 : 0 ≤ 64 * A * (Real.sqrt (B + 2) + 128) * finiteExtraReferenceConstant d ^ 2 *
      coreConvolutionConstant (finiteOmega d + 1) := by positivity
  have h2 : 0 ≤ 8 * finiteExtraReferenceConstant d ^ 2 * localizationExceptionalMass d (2 : ℂ) := by positivity
  have h3 : 0 ≤ 8 * finiteExtraReferenceConstant d ^ 2 *
      (((finiteOmega d : ℝ) + 1) / ((d : ℝ) - 1)) := by positivity
  linarith only [h1, h2, h3, hC]

end DeficientGraph

def sourceDeletionConstant (d : ℕ) (β B : ℝ) : ℝ :=
  let K := DeficientGraph.localizationWeakConstant d B (sourceLocalizationLogCap d β)
  modelDeletionLogConstant d B * (K + 1) + K

private theorem cut_error_scaled (a : ℕ) (L ε D c K : ℝ)
    (ha : 1 ≤ a) (hL : 1 ≤ L) (hε : 0 ≤ ε) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hD : D ≤ c * L ^ (2 * a)) (hcap : ε * L ^ (4 * a) ≤ 1) :
    D * ((K + 1) * L * ε) * L ≤ c * (K + 1) := by
  have hpow : L ^ (2 * a + 2) ≤ L ^ (4 * a) := pow_le_pow_right₀ hL (by omega)
  have he := (mul_le_mul_of_nonneg_left hpow hε).trans hcap
  have hleft := mul_le_mul_of_nonneg_right hD
    (show 0 ≤ (K + 1) * L * ε * L by positivity)
  have hright := mul_le_mul_of_nonneg_left he (show 0 ≤ c * (K + 1) by positivity)
  calc
    _ ≤ (c * L ^ (2 * a)) * ((K + 1) * L * ε * L) := by nlinarith only [hleft]
    _ = c * (K + 1) * (ε * L ^ (2 * a + 2)) := by rw [pow_add]; ring
    _ ≤ _ := by simpa using hright

structure SourceDeletionBounds (a d N : ℕ) (β B : ℝ) (z : ℂ) : Prop where
  localization : SourceLocalizationBounds a d N β B z
  depth_cap : ((actualCavityDepth a d N z - 1 : ℕ) : ℝ) + 1 ≤ Real.log (N : ℝ)
  reference_small : ∀ q : ℂ, ‖q - semicircleRoot z‖ ≤ scalarScale (spectralScale z)
    (graphPaperError a d N (logarithmicRadius β d N) z) →
    ‖q - semicircleRoot z‖ * finiteReferenceConstant d * coreConvolutionConstant (finiteOmega d) *
      ((6 * ((actualCavityDepth a d N z - 1) + logarithmicRadius β d N) + 2 : ℕ) + 1 : ℝ) ≤ 1 / 2
  deleted_small : ∀ q : ℂ, ‖q - semicircleRoot z‖ ≤ scalarScale (spectralScale z)
    (graphPaperError a d N (logarithmicRadius β d N) z) →
    ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d * coreConvolutionConstant (finiteOmega d + 1) *
      ((2 * logarithmicRadius β d N + (finiteOmega d + 2) * (2 * logarithmicRadius β d N + 1) : ℕ) + 1 : ℝ) ≤ 1 / 2
  cut_small : ∀ (g : RegularGraph N d) (o : Fin N),
    (Nat.card (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)) : ℝ) *
      DeficientGraph.boundarySchurConstant d B *
        ((DeficientGraph.localizationWeakConstant d B (sourceLocalizationLogCap d β) + 1) * Real.log (N : ℝ) *
          graphPaperError a d N (logarithmicRadius β d N) z) ≤ 1 / 2
  cut_scale : ∀ (g : RegularGraph N d) (o : Fin N),
    (Nat.card (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)) : ℝ) *
      ((DeficientGraph.localizationWeakConstant d B (sourceLocalizationLogCap d β) + 1) * Real.log (N : ℝ) *
        graphPaperError a d N (logarithmicRadius β d N) z) ≤ Real.log (N : ℝ)

/-- Every source Schur/deletion absorption budget holds at the actual
spectral-dependent depth, uniformly over all graphs and centers. -/
theorem eventually_sourceDeletionBounds (a b d : ℕ) (β B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hβ : 0 < β) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      SourceDeletionBounds a d N β B z := by
  let A := sourceLocalizationLogCap d β
  let K := DeficientGraph.localizationWeakConstant d B A
  let C := DeficientGraph.boundarySchurConstant d B
  let H := ((d : ℝ) + 1) * (K + 1)
  let Href := A * finiteReferenceConstant d * coreConvolutionConstant (finiteOmega d)
  let Hdel := A * finiteExtraReferenceConstant d * coreConvolutionConstant (finiteOmega d + 1)
  have hA : 0 ≤ A := sourceLocalizationLogCap_nonnegative d hd β hβ.le
  have hK : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans
    (DeficientGraph.localizationWeakConstant_ge_one d hd B A hA)
  have hCref : 0 ≤ finiteReferenceConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans
    (finiteReferenceConstant_ge_one d hd)
  have hCextra : 0 ≤ finiteExtraReferenceConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans
    (finiteExtraReferenceConstant_ge_one d hd)
  have hC0 := coreConvolutionConstant_nonnegative (finiteOmega d)
  have hC1 := coreConvolutionConstant_nonnegative (finiteOmega d + 1)
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hk : 0 < (d : ℝ) - 1 := by linarith
  have hC : 0 ≤ C := by dsimp [C, DeficientGraph.boundarySchurConstant]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hHref : 0 ≤ Href := by dsimp only [Href]; positivity
  have hHdel : 0 ≤ Hdel := by dsimp only [Hdel]; positivity
  have hdepthLarge := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_sourceLocalizationBounds a b d β B ha hb hd hβ,
    eventually_paperError_small a b d β ha hb hd hβ, eventually_actualCavityDepth_le_log a d hd,
    hdepthLarge, eventually_log_ge_nat (2 * Href), eventually_log_ge_nat (2 * Hdel),
    eventually_log_ge_nat H, eventually_log_ge_nat (2 * H * C)]
    with N hloc herr hdepth hdepthLarge hlargeRef hlargeDel hlargeH hlargeCut
  intro z hz hfloor
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let ell := actualCavityDepth a d N z - 1
  have S := hloc z hz hfloor
  have hL : 1 ≤ L := S.log_one
  have hLp : 0 < L := by linarith
  have hε : 0 ≤ ε := S.error_nonnegative
  have hfullCap : ε * L ^ (4 * a) ≤ 1 := by
    exact (le_div_iff₀ (pow_pos hLp _)).mp (by simpa only [one_div] using herr z hz hfloor)
  have hellUpper := (actualCavityDepth_radius_bounds a d N z hdepthLarge).2
  have hdepthPos : 1 ≤ actualCavityDepth a d N z := by
    have hh := (nonresonantDepth_bounds (semicircleRoot z) (baselineCavityDepth a d N)).1
    change baselineCavityDepth a d N ≤ actualCavityDepth a d N z at hh
    dsimp only [baselineCavityDepth] at hh
    omega
  have hdepthCap : (ell : ℝ) + 1 ≤ L := by
    have heq : ell + 1 = actualCavityDepth a d N z := by dsimp only [ell]; omega
    have heqR : (ell : ℝ) + 1 = (actualCavityDepth a d N z : ℝ) := by exact_mod_cast heq
    rw [heqR]
    exact hdepth z
  have hcutScaled (g : RegularGraph N d) (o : Fin N) :
      (Nat.card (graphBallVertices g.graph o ell) : ℝ) * ((K + 1) * L * ε) * L ≤ H := by
    have hnat := g.ball_card_sharp o ell hd
    have hnatR : (Nat.card (graphBallVertices g.graph o ell) : ℝ) ≤
        ((d : ℝ) + 1) * (((d - 1 : ℕ) : ℝ) ^ ell) := by exact_mod_cast hnat
    have hk : (1 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ d - 1 by omega)
    have hpower := (pow_le_pow_right₀ hk hellUpper).trans (doubleLogRadius_base_power_bound a d N hd hL)
    have hsize := hnatR.trans (mul_le_mul_of_nonneg_left hpower (by positivity : 0 ≤ (d : ℝ) + 1))
    exact cut_error_scaled a L ε _ ((d : ℝ) + 1) K (by omega) hL hε (by positivity) hK hsize hfullCap
  refine ⟨S, hdepthCap, ?_, ?_, ?_, ?_⟩
  · intro q hprior
    have hδ := weak_prior_scaled_norm z q hz ε L hε S.error_scaled hprior
    have hh := scale_weight_small _ L Href (norm_nonneg _) hLp hHref hδ hlargeRef
    calc
      _ ≤ ‖q - semicircleRoot z‖ * finiteReferenceConstant d * coreConvolutionConstant (finiteOmega d) * (A * L) :=
        mul_le_mul_of_nonneg_left S.full_cap (by positivity)
      _ = ‖q - semicircleRoot z‖ * Href * L := by dsimp only [Href]; ring
      _ ≤ _ := hh
  · intro q hprior
    have hδ := weak_prior_scaled_norm z q hz ε L hε S.error_scaled hprior
    have hh := scale_weight_small _ L Hdel (norm_nonneg _) hLp hHdel hδ hlargeDel
    calc
      _ ≤ ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d * coreConvolutionConstant (finiteOmega d + 1) * (A * L) :=
        mul_le_mul_of_nonneg_left S.deleted_cap (by positivity)
      _ = ‖q - semicircleRoot z‖ * Hdel * L := by dsimp only [Hdel]; ring
      _ ≤ _ := hh
  · intro g o
    apply (mul_le_mul_right hLp).mp
    have hh := mul_le_mul_of_nonneg_right (hcutScaled g o) hC
    change (Nat.card (graphBallVertices g.graph o ell) : ℝ) * C * ((K + 1) * L * ε) * L ≤ _
    nlinarith only [hh, hlargeCut]
  · intro g o
    apply (mul_le_mul_right hLp).mp
    exact (hcutScaled g o).trans (hlargeH.trans (by nlinarith only [hL]))

end LocalLaw
