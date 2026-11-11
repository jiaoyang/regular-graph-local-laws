import LocalLaw.AbsoluteEffectiveHalfTail
import LocalLaw.ParameterSmallness

/-! Scalar absorption for conservative whole-UPPER omitted-T decay. -/
namespace LocalLaw

theorem log_error_power_budget (a m p:ℕ)(L ε K:ℝ)(hL:1≤L)(hε:0≤ε)(_hK:0≤K)
    (hKL:K≤L)(hexp:m+p+1≤4*a)(hcap:ε*L^(4*a)≤1):
    K*L^m*ε≤1/L^p:=by
  have hLp:0<L:=by linarith
  apply (le_div_iff₀ (pow_pos hLp p)).mpr
  calc
    _=K*L^(m+p)*ε:=by rw [pow_add];ring
    _≤L*L^(m+p)*ε:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKL (pow_nonneg hLp.le _)) hε
    _=L^(m+p+1)*ε:=by rw [pow_succ];ring
    _≤L^(4*a)*ε:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL hexp) hε
    _≤1:=by simpa only [mul_comm] using hcap

noncomputable section

theorem eventually_omitted_inner_whole_error_budget (a b d:ℕ)(β K:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hβ:0<β)(hK:0≤K):
    ∀ᶠ N:ℕ in Filter.atTop,∀z:ℂ,0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      K*(Real.log (N:ℝ)^(3*a-3)*physicalTransfer d z^(effectiveModelRadius a d N β/2-1)+
        Real.log (N:ℝ)^(3*a-2)*graphPaperError a d N (logarithmicRadius β d N) z)≤
        1/Real.log (N:ℝ):=by
  filter_upwards [eventually_effective_half_tail_log_budget a d (3*a-3) 1 β (2*K) hd hβ (by positivity),
    eventually_paperError_small a b d β ha hb hd hβ,
    eventually_log_ge_nat (2*K),eventually_log_ge_nat 1,Filter.eventually_ge_atTop 1]
    with N htail hsmall hlarge hlog hN
  intro z hz hfloor
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  have hLp:0<L:=by dsimp only [L];linarith
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hcap:ε*L^(4*a)≤1:=by
    apply (le_div_iff₀ (pow_pos hLp _)).mp
    simpa only [one_div] using hsmall z hz hfloor
  have he:=log_error_power_budget a (3*a-2) 1 L ε (2*K) hlog hε (by positivity) hlarge (by omega) hcap
  have ht:=htail z
  simp only [pow_one] at he ht
  change K*(L^(3*a-3)*physicalTransfer d z^(effectiveModelRadius a d N β/2-1)+L^(3*a-2)*ε)≤1/L
  nlinarith only [he,ht]

end
end LocalLaw
