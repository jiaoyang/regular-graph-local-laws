import LocalLaw.OmittedInnerLogBudget
import LocalLaw.ParameterSmallness

/-! Actual nominal error and effective radius realize the one-sided budget. -/
noncomputable section
namespace LocalLaw

theorem eventually_omitted_inner_error_budget (a b d:ℕ)(c β K:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hK:0≤K):
    ∀ᶠ N:ℕ in Filter.atTop,∀z:ℂ,0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      K*Real.log (N:ℝ)^(3*a-4)*
        (physicalTransfer d z^(effectiveModelRadius a d N β)+graphPaperError a d N (logarithmicRadius β d N) z)≤
          1/Real.log (N:ℝ):=by
  let k:ℝ:=((d-1:ℕ):ℝ)
  filter_upwards [eventually_paperError_small a b d β ha hb hd hβ,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_log_ge_nat (K*(k^2+1)),eventually_log_ge_nat 1,Filter.eventually_ge_atTop 1]
    with N hsmall hradius hlarge hlog hN
  intro z hz hfloor
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let t:=physicalTransfer d z^(effectiveModelRadius a d N β)
  have hLp:0<L:=by dsimp only [L];linarith
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have ht:0≤t:=pow_nonneg (physicalTransfer_pos d hd z).le _
  have hcap:ε*L^(4*a)≤1:=by
    apply (le_div_iff₀ (pow_pos hLp _)).mp
    simpa only [one_div] using hsmall z hz hfloor
  have htail:=effectiveModelRadius_localization_tail a d N β hd hlog hradius.1 z hz.le
  have htPower:t^2=physicalTransfer d z^(2*effectiveModelRadius a d N β):=by
    dsimp only [t]
    rw [←pow_mul]
    congr 1
    omega
  rw [←htPower] at htail
  have htail':L^(4*a)*t^2≤k^4*ε:=by
    have hh: t^2*L^(4*a)≤k^4*ε:=(le_div_iff₀ (pow_pos hLp _)).mp htail
    simpa only [mul_comm] using hh
  exact one_sided_omitted_log_budget a L ε t k K (by omega) hlog hε ht hK hcap htail' hlarge

end LocalLaw
