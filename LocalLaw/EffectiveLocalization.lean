import LocalLaw.EffectiveModelRadius
import LocalLaw.SourceLocalizationParameters

/-!
# Finite localization at the effective radius and nominal error

Only the model radius is shortened. Every weak prior, scaled error,
inflation branch and logarithmic budget is retained at the nominal radius.
The proved log-log loss estimate supplies the shorter-radius tail.
-/

noncomputable section
namespace LocalLaw

/-- A fixed degree-dependent lower bound on log N absorbs the radius-loss
constant. The error on the right is still at the nominal radius. -/
theorem effectiveModelRadius_tail_le_nominal_error (a d N : ℕ) (β : ℝ)
    (ha : 1 ≤ a) (hd : 3 ≤ d) (hlog : ((d - 1 : ℕ) : ℝ) ≤ Real.log (N : ℝ))
    (hroom : modelRadiusLoss a d N ≤ logarithmicRadius β d N) (z : ℂ) (hz : 0 ≤ z.im) :
    physicalTransfer d z ^ (2 * effectiveModelRadius a d N β) ≤
      graphPaperError a d N (logarithmicRadius β d N) z := by
  let k : ℝ := ((d - 1 : ℕ) : ℝ)
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  have hk : 1 ≤ k := by dsimp only [k]; exact_mod_cast (show 1 ≤ d - 1 by omega)
  have hL : 1 ≤ L := hk.trans hlog
  have hLp : 0 < L := by linarith
  have hpow : k ^ 4 ≤ L ^ (4 * a) :=
    (pow_le_pow_left₀ (by positivity) hlog 4).trans (pow_le_pow_right₀ hL (by omega))
  have hε : 0 ≤ ε := by
    have hh := graphPaperError_lower a d N (logarithmicRadius β d N) z hL hz
    have hn : 0 ≤ localizationErrorFloor a d N (logarithmicRadius β d N) := by
      unfold localizationErrorFloor
      positivity
    exact hn.trans hh
  apply (effectiveModelRadius_localization_tail a d N β hd hL hroom z hz).trans
  change k ^ 4 * ε / L ^ (4 * a) ≤ ε
  apply (div_le_iff₀ (pow_pos hLp _)).mpr
  simpa only [mul_comm ε] using mul_le_mul_of_nonneg_right hpow hε

namespace SourceLocalizationBounds
variable {a d N : ℕ} {β B : ℝ} {z : ℂ}

private theorem effective_pair_cap (S : SourceLocalizationBounds a d N β B z) :
    (((4 * effectiveModelRadius a d N β + 1 : ℕ) + 1 : ℝ)) ≤
      sourceLocalizationLogCap d β * Real.log (N : ℝ) := by
  have hr : effectiveModelRadius a d N β ≤ logarithmicRadius β d N := Nat.sub_le _ _
  have hnat : 4 * effectiveModelRadius a d N β + 1 + 1 ≤ 4 * logarithmicRadius β d N + 1 + 1 := by omega
  have hcast : (((4 * effectiveModelRadius a d N β + 1 : ℕ) + 1 : ℝ)) ≤
      (((4 * logarithmicRadius β d N + 1 : ℕ) + 1 : ℝ)) := by exact_mod_cast hnat
  exact hcast.trans S.pair_cap

/-- Actual full-model localization with the shortened internal model radius
and the original weak prior/error; the nominal geometry cap may be reused. -/
theorem full_model_effective {U : Type} [Fintype U] [DecidableEq U]
    (S : SourceLocalizationBounds a d N β B z) (ha : 1 ≤ a) (hd : 3 ≤ d) (hβ : 0 ≤ β)
    (hlog : ((d - 1 : ℕ) : ℝ) ≤ Real.log (N : ℝ))
    (hroom : modelRadiusLoss a d N ≤ logarithmicRadius β d N)
    (model : DeficientGraph U d) (hclass : model.ComponentFiniteReferenceBudget)
    (q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (hB : ‖z‖ ≤ B)
    (hprior : ‖q - semicircleRoot z‖ ≤ scalarScale (spectralScale z)
      (graphPaperError a d N (logarithmicRadius β d N) z))
    (hdiam : ∀ u v, model.graph.dist u v ≤ 6 * ((actualCavityDepth a d N z - 1) + logarithmicRadius β d N) + 2)
    (u v : U) :
    ‖model.extensionGreen q z u v - model.P (effectiveModelRadius a d N β) z q u v‖ ≤
      DeficientGraph.localizationWeakConstant d B (sourceLocalizationLogCap d β) * Real.log (N : ℝ) *
        graphPaperError a d N (logarithmicRadius β d N) z :=
  model.componentwise_weak_pair_localization hd hclass q z hz hq B hB _ _ _ S.error_nonnegative S.log_one
    (sourceLocalizationLogCap_nonnegative d hd β hβ) S.error_scaled hprior _ _ hdiam
    S.full_cap S.effective_pair_cap S.large_log
    (effectiveModelRadius_tail_le_nominal_error a d N β ha hd hlog hroom z hz.le) u v

/-- The actual inherited-deficit deleted model uses the same nominal-error
budgets at the effective internal radius. -/
theorem deleted_model_effective {U : Type} [Fintype U] [DecidableEq U]
    (S : SourceLocalizationBounds a d N β B z) (ha : 1 ≤ a) (hd : 3 ≤ d) (hβ : 0 ≤ β)
    (hlog : ((d - 1 : ℕ) : ℝ) ≤ Real.log (N : ℝ))
    (hroom : modelRadiusLoss a d N ≤ logarithmicRadius β d N)
    (model : DeficientGraph U d) (hclass : model.ComponentFiniteReferenceBudget)
    (q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (hB : ‖z‖ ≤ B)
    (hprior : ‖q - semicircleRoot z‖ ≤ scalarScale (spectralScale z)
      (graphPaperError a d N (logarithmicRadius β d N) z))
    (hdiam : ∀ u v, model.graph.dist u v ≤ 2 * logarithmicRadius β d N + (finiteOmega d + 2) *
      (2 * logarithmicRadius β d N + 1))
    (u v : U) :
    ‖model.extensionGreen q z u v - model.P (effectiveModelRadius a d N β) z q u v‖ ≤
      DeficientGraph.localizationWeakConstant d B (sourceLocalizationLogCap d β) * Real.log (N : ℝ) *
        graphPaperError a d N (logarithmicRadius β d N) z :=
  model.componentwise_weak_pair_localization hd hclass q z hz hq B hB _ _ _ S.error_nonnegative S.log_one
    (sourceLocalizationLogCap_nonnegative d hd β hβ) S.error_scaled hprior _ _ hdiam
    S.deleted_cap S.effective_pair_cap S.large_log
    (effectiveModelRadius_tail_le_nominal_error a d N β ha hd hlog hroom z hz.le) u v

end SourceLocalizationBounds
end LocalLaw
