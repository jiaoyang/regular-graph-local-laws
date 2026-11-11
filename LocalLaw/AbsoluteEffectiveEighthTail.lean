import LocalLaw.EffectiveModelRadius
import LocalLaw.ParameterGrowth

/-! Every fixed logarithmic budget is absorbed at one eighth of the effective radius. -/
noncomputable section
namespace LocalLaw

theorem eventually_effective_eighth_tail_log_budget (a d m p:ℕ)(β K:ℝ)
    (hd:3≤d)(hβ:0<β)(hK:0≤K):
    ∀ᶠ N:ℕ in Filter.atTop,∀z:ℂ,
      K*Real.log (N:ℝ)^m*physicalTransfer d z^(effectiveModelRadius a d N β/8-1)≤
        1/Real.log (N:ℝ)^p:=by
  let M:=32*(m+p+1)
  filter_upwards [eventually_resampling_radius_margin a d 4 40 β hd hβ,
    eventually_localization_log_budget β d M hβ hd,eventually_log_ge_nat K,eventually_log_ge_nat 1]
    with N hradius hbudget hKlog hlog
  intro z
  let L:=Real.log (N:ℝ)
  let rn:=logarithmicRadius β d N
  let n:=effectiveModelRadius a d N β/8-1
  let ρ:=physicalTransfer d z
  let x:=K*L^(m+p)*ρ^n
  have hLp:0<L:=by dsimp only [L];linarith
  have hρ0:0≤ρ:=(physicalTransfer_pos d hd z).le
  have hρ1:ρ≤1:=by dsimp only [ρ];nlinarith [physicalTransfer_sq_le_half d hd z]
  have hn:rn≤16*n:=by
    dsimp only [rn,n,effectiveModelRadius,modelRadiusLoss]
    omega
  have h32:2*rn≤32*n:=by omega
  have hpow:(K*L^(m+p)*ρ^n)^32≤1:=by
    have hp:(K*L^(m+p)*ρ^n)^32≤L^M*ρ^(2*rn):=by
      calc
        _≤(L*L^(m+p)*ρ^n)^32:=by
          apply pow_le_pow_left₀ (by positivity)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hKlog (pow_nonneg hLp.le _)) (pow_nonneg hρ0 _)
        _=L^M*ρ^(32*n):=by
          rw [show L*L^(m+p)=L^(m+p+1) by rw [pow_succ];ring,mul_pow,←pow_mul,←pow_mul]
          dsimp only [M]
          simp only [Nat.mul_comm]
        _≤_:=mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0 hρ1 h32) (pow_nonneg hLp.le _)
    have ht:ρ^(2*rn)≤((((d-1:ℕ):ℝ)^rn)⁻¹):=physical_transfer_two_sided_tail d hd z rn
    calc
      _≤L^M*((((d-1:ℕ):ℝ)^rn)⁻¹):=hp.trans (mul_le_mul_of_nonneg_left ht (pow_nonneg hLp.le _))
      _≤L^M*(1/(3*L^M)):=mul_le_mul_of_nonneg_left hbudget (pow_nonneg hLp.le _)
      _=(1:ℝ)/3:=by field_simp;ring
      _≤1:=by norm_num
  have hx0:0≤x:=by dsimp only [x];positivity
  have hx:x≤1:=by
    classical
    by_contra hh
    have hx1:1<x:=lt_of_not_ge hh
    have hp:1<x^32:=one_lt_pow₀ hx1 (by norm_num:32≠0)
    exact not_lt_of_ge hpow hp
  apply (le_div_iff₀ (pow_pos hLp p)).mpr
  calc
    _=x:=by dsimp only [x];rw [pow_add];ring
    _≤1:=hx

end LocalLaw
