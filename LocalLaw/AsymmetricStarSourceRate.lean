import LocalLaw.EffectiveTailCounting

/-! # The finite restored-star bound at the actual nominal prime rate

The local harmonic residual may be L² epsilon. The true harmonic L1
weights cost at most L; the core localization tail may carry n L².
These precise losses still fit epsilon-prime with the nominal radius fixed.
-/

open Filter
noncomputable section
namespace LocalLaw

theorem eventually_asymmetric_star_source_rate (a d:ℕ)(β Count KM KP D C H m V:ℝ)
    (ha:12≤a)(hd:3≤d)(hCount:0≤Count)(_hKM:0≤KM)(_hKP:0≤KP)(_hD:0≤D)
    (_hC:0≤C)(_hH:0≤H)(_hm:0 ≤ m)(hV:0≤V) :
    ∀ᶠ N:ℕ in atTop,∀z:ℂ,0≤z.im→
      modelRadiusLoss a d N≤logarithmicRadius β d N→
      ∀n:ℝ,0≤n→n≤Count*Real.log (N:ℝ)^(2*a)→
      let L:=Real.log (N:ℝ)
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      let ρ:=physicalTransfer d z
      (KM*L*ε)*(H*L)*(H*L)+m^2*(KP*L)^2*(V*(n+1)*L^2)*ρ^(2*effectiveModelRadius a d N β)+
        C*(D*L^2*ε)*m*(H*L+H*L)≤(KM*H^2+1+2*C*D*m*H)*(L^3*ε) := by
  let M:=m^2*KP^2*V
  have hM:0≤M:=by dsimp only [M];positivity
  filter_upwards [eventually_effective_tail_counting a d β (Count+1) M ha hd (by positivity) hM,
    eventually_log_ge_nat 1,eventually_ge_atTop 1] with N htail hlog hN
  intro z hz hroom n hn hncap
  dsimp only
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let ρ:=physicalTransfer d z
  have hLp:0<L:=by dsimp only [L];linarith
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz
  have hcount:n+1≤(Count+1)*L^(2*a):=by
    have hp:1≤L^(2*a):=one_le_pow₀ hlog
    nlinarith only [hncap,hp]
  have ht:=htail z hz hroom (n+1) (by linarith) hcount
  have ht':M*(n+1)*ρ^(2*effectiveModelRadius a d N β)*L^4≤ε:=by
    have hh:=mul_le_mul_of_nonneg_right ht (pow_nonneg hLp.le 4)
    have hpow:L^4≤L^16:=pow_le_pow_right₀ hlog (by omega)
    have hratio:ε/L^16*L^4≤ε:=by
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ (pow_pos hLp 16)).mpr (mul_le_mul_of_nonneg_left hpow hε)
    exact hh.trans hratio
  have htailFinal:m^2*(KP*L)^2*(V*(n+1)*L^2)*ρ^(2*effectiveModelRadius a d N β)≤L^3*ε:=by
    have he:m^2*(KP*L)^2*(V*(n+1)*L^2)*ρ^(2*effectiveModelRadius a d N β)=
        M*(n+1)*ρ^(2*effectiveModelRadius a d N β)*L^4:=by dsimp only [M];ring
    rw [he]
    exact ht'.trans (le_mul_of_one_le_left hε (one_le_pow₀ hlog))
  have hmain:(KM*L*ε)*(H*L)*(H*L)=KM*H^2*(L^3*ε):=by ring
  have hres:C*(D*L^2*ε)*m*(H*L+H*L)=(2*C*D*m*H)*(L^3*ε):=by ring
  rw [hmain,hres]
  nlinarith only [htailFinal]

end LocalLaw
