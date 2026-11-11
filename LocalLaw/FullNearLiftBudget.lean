import LocalLaw.AbsoluteEffectiveHalfTail

/-! # Uniform full inner-set lifting at the quarter-close margin

The ordinary exterior error pays the actual two harmonic L1 weights. The
remaining spatial tail is absorbed absolutely, keeping the nominal error.
-/

noncomputable section
namespace LocalLaw

theorem eventually_full_near_lift_budget (a b d:ℕ)(β Count K H:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hβ:0<β)(hCount:0≤Count)(hK:0≤K)(_hH:0≤H):
    ∀ᶠ N:ℕ in Filter.atTop,∀z:ℂ,0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      ∀loss:ℕ,loss≤effectiveModelRadius a d N β/2→∀ mass : ℝ,0 ≤ mass→mass ≤ Count*Real.log (N:ℝ)^(2*a)→
      let L:=Real.log (N:ℝ)
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      let ρ:=physicalTransfer d z
      (K*L*ε+K*(mass+1)*L^4*ρ^(2*(effectiveModelRadius a d N β-loss)))*(H*L^(2*a-2))^2≤
        (K*H^2+1)/L := by
  have hcoef:0≤K*(Count+1)*H^2:=by positivity
  filter_upwards [eventually_effective_half_tail_log_budget a d (6*a) 1 β (K*(Count+1)*H^2) hd hβ hcoef,
    eventually_paperError_small a b d β ha hb hd hβ,eventually_log_ge_nat 1]
    with N htail hpaper hlog
  intro z hz hfloor loss hloss mass hmass hcount
  dsimp only
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let ρ:=physicalTransfer d z
  let r:=effectiveModelRadius a d N β
  have hLp:0<L:=by dsimp only [L];linarith
  have hε:0≤ε:=by
    have hh:=hpaper z hz hfloor
    exact graphPaperError_nonnegative a d N _ z (by
      by_contra hn
      have hN:N=0:=by omega
      subst N
      norm_num at hlog) hz.le
  have hcap:L^(4*a)*ε≤1:=(mul_comm _ _).le.trans (by
    have hh:ε*L^(4*a)≤1:=(le_div_iff₀ (pow_pos hLp _)).mp (by simpa only [one_div] using hpaper z hz hfloor)
    exact hh)
  have hordinary:L^(4*a-3)*ε≤1/L:=by
    apply (le_div_iff₀ hLp).mpr
    calc
      _=L^(4*a-2)*ε:=by rw [show 4*a-2=(4*a-3)+1 by omega,pow_succ];ring
      _≤L^(4*a)*ε:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hlog (by omega)) hε
      _≤1:=hcap
  have hmain:(K*L*ε)*(H*L^(2*a-2))^2≤K*H^2/L:=by
    have he:(K*L*ε)*(H*L^(2*a-2))^2=(K*H^2)*(L^(4*a-3)*ε):=by
      rw [mul_pow,←pow_mul]
      have hn:4*a-3=1+(2*a-2)*2:=by omega
      rw [hn,pow_add,pow_one]
      ring
    rw [he]
    exact (mul_le_mul_of_nonneg_left hordinary (by positivity)).trans_eq (by ring)
  have hρ:0≤ρ:=(physicalTransfer_pos d hd z).le
  have hρone:ρ≤1:=by dsimp only [ρ];nlinarith [physicalTransfer_sq_le_half d hd z]
  have hp:ρ^(2*(r-loss))≤ρ^(r/2-1):=pow_le_pow_of_le_one hρ hρone (by dsimp only [r] at *;omega)
  have hmasscap:mass+1≤(Count+1)*L^(2*a):=by
    have hh:1≤L^(2*a):=one_le_pow₀ hlog
    nlinarith only [hcount,hh]
  have htailPart:(K*(mass+1)*L^4*ρ^(2*(r-loss)))*(H*L^(2*a-2))^2≤1/L:=by
    calc
      _≤(K*((Count+1)*L^(2*a))*L^4*ρ^(r/2-1))*(H*L^(2*a-2))^2:=by gcongr
      _=(K*(Count+1)*H^2)*L^(6*a)*ρ^(r/2-1):=by
        rw [mul_pow,←pow_mul]
        have hn:6*a=2*a+4+(2*a-2)*2:=by omega
        rw [hn,pow_add,pow_add]
        ring
      _≤1/L:=by simpa only [pow_one] using htail z
  rw [add_mul]
  exact (add_le_add hmain htailPart).trans_eq (by ring)

end LocalLaw
