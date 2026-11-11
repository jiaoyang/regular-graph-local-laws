import LocalLaw.ComponentFiniteLocalization
import LocalLaw.PairRestrictionIdentity
import LocalLaw.PairModelReferenceBounds
import LocalLaw.EffectiveModelRadius

/-!
# Physical reference correction between internal and nominal radii

At q=msc the ordinary spectral feedback vanishes exactly. Actual finite
pair localization therefore compares two reference radii using only its
proved two-sided tail. This restores the nominal model after a bootstrap
using a shorter internal radius, without comparing inflated-error branches.
-/

noncomputable section
namespace LocalLaw
local instance referenceRadiusDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def referenceRadiusConstant (d : ℕ) : ℝ :=
  8 * finiteExtraReferenceConstant d ^ 2 * DeficientGraph.localizationExceptionalMass d (2 : ℂ) +
    8 * finiteExtraReferenceConstant d ^ 2 * (((finiteOmega d : ℝ) + 1) / ((d : ℝ) - 1)) +
    2 * finiteExtraReferenceConstant d

private theorem reference_localization_expression (d : ℕ) (hd : 3 ≤ d) (z : ℂ) (B : ℝ) (R r : ℕ) :
    DeficientGraph.finitePairLocalizationBound d (semicircleRoot z) z B R r ≤
      referenceRadiusConstant d * physicalTransfer d z ^ (2 * r) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hk : 0 < (d : ℝ) - 1 := by linarith
  have hm : ‖semicircleRoot z‖ ≤ 2 := (semicircleRoot_norm_le_one z).trans (by norm_num)
  have hM : DeficientGraph.localizationExceptionalMass d (semicircleRoot z) ≤
      DeficientGraph.localizationExceptionalMass d (2 : ℂ) := by
    unfold DeficientGraph.localizationExceptionalMass
    have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
    rw [htwo]
    exact div_le_div_of_nonneg_right (add_le_add_left
      (mul_le_mul_of_nonneg_right hm (by positivity)) _) hk.le
  have hfirst := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 8 * finiteExtraReferenceConstant d ^ 2)
  have hsecond := mul_le_mul_of_nonneg_right hm (by positivity :
    0 ≤ 4 * finiteExtraReferenceConstant d ^ 2 * (((finiteOmega d : ℝ) + 1) / ((d : ℝ) - 1)))
  have hcoef : 8 * finiteExtraReferenceConstant d ^ 2 *
        DeficientGraph.localizationExceptionalMass d (semicircleRoot z) +
      4 * finiteExtraReferenceConstant d ^ 2 * ‖semicircleRoot z‖ *
        (((finiteOmega d : ℝ) + 1) / ((d : ℝ) - 1)) + 2 * finiteExtraReferenceConstant d ≤
        referenceRadiusConstant d := by
    unfold referenceRadiusConstant
    nlinarith only [hfirst, hsecond]
  have htail : 0 ≤ physicalTransfer d z ^ (2 * r) := pow_nonneg (norm_nonneg _) _
  unfold DeficientGraph.finitePairLocalizationBound DeficientGraph.ordinaryFeedbackBudget
  simp only [sub_self, norm_zero, mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero, zero_add]
  exact mul_le_mul_of_nonneg_right hcoef htail

namespace RegularGraph
variable {N d : ℕ}

/-- Actual pair models at two radii, under the original structural ball
bound. No radius-comparison or localization estimate is supplied. -/
theorem pairP_reference_radius_comparison (g : RegularGraph N d) (hd : 3 ≤ d)
    (rSmall rLarge R : ℕ) (hr : rSmall ≤ rLarge) (hmargin : 4 * rLarge + 1 ≤ R)
    (hballs : ∀ o, graphBallExcess g.graph o R ≤ finiteOmega d)
    (z : ℂ) (hz : 0 < z.im) (i j : Fin N) :
    ‖g.P rLarge z (semicircleRoot z) i j - g.P rSmall z (semicircleRoot z) i j‖ ≤
      referenceRadiusConstant d * physicalTransfer d z ^ (2 * rSmall) := by
  let M := g.pairModel i j rLarge
  let ii := pairBallLeft g.graph i j rLarge
  let jj := pairBallRight g.graph i j rLarge
  have hclass := (g.pairModel_componentReferenceBudget i j rLarge R hmargin hballs).to_componentFinite
  have hlocal := M.componentwise_pair_localization hd hclass (semicircleRoot z) z hz
    (semicircleRoot_im_pos hz).le ‖z‖ le_rfl (4 * rLarge + 1) rSmall
    (pairBall_distance_bound g.graph i j rLarge)
    (by simp) (by simp) (by simp) (by simp)
    (by simp [DeficientGraph.ordinaryFeedbackBudget]) ii jj
  change ‖M.extensionGreen (semicircleRoot z) z ii jj - M.P rSmall z (semicircleRoot z) ii jj‖ ≤ _ at hlocal
  have hi : graphBallVertices g.graph i rSmall ⊆ pairBallVertices g.graph i j rLarge :=
    fun _ hv => Or.inl (hv.trans (ENat.coe_le_coe.mpr hr))
  have hj : graphBallVertices g.graph j rSmall ⊆ pairBallVertices g.graph i j rLarge :=
    fun _ hv => Or.inr (hv.trans (ENat.coe_le_coe.mpr hr))
  have hrestrict := g.deficient.restrict_pair_P (pairBallVertices g.graph i j rLarge) ii jj rSmall hi hj
    (semicircleRoot z) z
  rw [g.deficient_P] at hrestrict
  have hlarge := g.pairModel_P i j rLarge (semicircleRoot z) z
  have hsmall : M.P rSmall z (semicircleRoot z) ii jj = g.P rSmall z (semicircleRoot z) i j := hrestrict
  rw [hlarge, hsmall] at hlocal
  exact hlocal.trans (reference_localization_expression d hd z ‖z‖ (4 * rLarge + 1) rSmall)

/-- Nominal-reference correction at the actual shorter radius, expressed in
the unchanged nominal paper error with a logarithmic gain. -/
theorem effective_reference_radius_correction (g : RegularGraph N d) (hd : 3 ≤ d)
    (a : ℕ) (β : ℝ) (R : ℕ)
    (hmargin : 4 * logarithmicRadius β d N + 1 ≤ R)
    (hballs : ∀ o, graphBallExcess g.graph o R ≤ finiteOmega d)
    (hlog : 1 ≤ Real.log (N : ℝ))
    (hroom : modelRadiusLoss a d N ≤ logarithmicRadius β d N)
    (z : ℂ) (hz : 0 < z.im) (i j : Fin N) :
    ‖g.P (logarithmicRadius β d N) z (semicircleRoot z) i j -
      g.P (effectiveModelRadius a d N β) z (semicircleRoot z) i j‖ ≤
      referenceRadiusConstant d * (((d - 1 : ℕ) : ℝ) ^ 4) *
        graphPaperError a d N (logarithmicRadius β d N) z / Real.log (N : ℝ) ^ (4 * a) := by
  have hC : 0 ≤ referenceRadiusConstant d := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hk : 0 < (d : ℝ) - 1 := by linarith
    have hExtra : 0 ≤ finiteExtraReferenceConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans
      (finiteExtraReferenceConstant_ge_one d hd)
    unfold referenceRadiusConstant DeficientGraph.localizationExceptionalMass
    positivity
  have hh := g.pairP_reference_radius_comparison hd (effectiveModelRadius a d N β) (logarithmicRadius β d N) R (Nat.sub_le _ _) hmargin hballs z hz i j
  have htail := mul_le_mul_of_nonneg_left
    (effectiveModelRadius_localization_tail a d N β hd hlog hroom z hz.le) hC
  exact hh.trans (htail.trans_eq (by ring))

end RegularGraph
end LocalLaw
