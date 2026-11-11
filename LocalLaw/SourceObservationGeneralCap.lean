import LocalLaw.SourceObservationParameters

/-! The observation budgets support any fixed larger logarithmic diameter cap. -/
namespace LocalLaw

theorem eventually_sourceObservationBounds_of_cap (a b d : ℕ) (c β B C1 A : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) (hA : sourceObservationLogCap d β≤A) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ, 0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      SourceObservationBounds d (effectiveModelRadius a d N β) z B C1
        (graphPaperError a d N (logarithmicRadius β d N) z) (Real.log (N:ℝ)) A := by
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_log_ge_nat (DeficientGraph.localizationBudgetConstant d B A),
    eventually_log_ge_nat (DeficientGraph.localizationWeakConstant d B A*C1)] with N hbase hlarge hfeedback
  intro z hz hfloor
  have S:=hbase z hz hfloor
  have hL : 0≤Real.log (N:ℝ) := (by norm_num : (0:ℝ)≤1).trans S.log_one
  have hcap : sourceObservationLogCap d β*Real.log (N:ℝ)≤A*Real.log (N:ℝ) :=
    mul_le_mul_of_nonneg_right hA hL
  exact ⟨S.error_nonnegative,S.log_one,S.log_cap_nonnegative.trans hA,S.coefficient_one,S.error_scaled,
    S.diameter_log.trans hcap,S.pair_log.trans hcap,hlarge,
    hfeedback.trans (by nlinarith only [S.log_one]),S.pivot_large,S.tail⟩

end LocalLaw
