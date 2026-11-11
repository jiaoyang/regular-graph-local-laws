import LocalLaw.AbsoluteEffectiveEighthTail
import LocalLaw.OmittedInnerWholeParameters

/-! Logarithmic absorption of the far inner-restoration correction. -/
namespace LocalLaw

theorem far_inner_log_budget (a:ℕ)(L ε t K:ℝ)(ha:12≤a)(hL:1≤L)(hε:0≤ε)(_ht:0≤t)
    (hK:0≤K)(hlarge:4*K≤L)(hcap:ε*L^(4*a)≤1)
    (htail:4*K*L^(7*a-5)*t^2≤1/L):
    K*L^(3*a-5)*(L^(2*a)*t+L^(2*a+1)*ε)^2≤1/L:=by
  have hL0:0≤L:=by linarith
  have hLp:0<L:=by linarith
  have hsquare:(L^(2*a)*t+L^(2*a+1)*ε)^2≤
      2*((L^(2*a)*t)^2+(L^(2*a+1)*ε)^2):=by nlinarith [sq_nonneg (L^(2*a)*t-L^(2*a+1)*ε)]
  have hmain:=mul_le_mul_of_nonneg_left hsquare (show 0≤K*L^(3*a-5) by positivity)
  have hp1:L^(3*a-5)*(L^(2*a)*t)^2=L^(7*a-5)*t^2:=by
    calc
      _=(L^(3*a-5)*L^((2*a)*2))*t^2:=by rw [mul_pow,←pow_mul];ring
      _=L^((3*a-5)+(2*a)*2)*t^2:=by rw [pow_add]
      _=_:=by rw [show (3*a-5)+(2*a)*2=7*a-5 by omega]
  have hp2:L^(3*a-5)*(L^(2*a+1)*ε)^2=L^(7*a-3)*ε^2:=by
    calc
      _=(L^(3*a-5)*L^((2*a+1)*2))*ε^2:=by rw [mul_pow,←pow_mul];ring
      _=L^((3*a-5)+(2*a+1)*2)*ε^2:=by rw [pow_add]
      _=_:=by rw [show (3*a-5)+(2*a+1)*2=7*a-3 by omega]
  have hcap2:ε^2*L^(4*(2*a))≤1:=by
    have hh:=mul_self_le_mul_self (by positivity:0≤ε*L^(4*a)) hcap
    have heq:ε^2*L^(4*(2*a))=(ε*L^(4*a))*(ε*L^(4*a)):=by
      calc
        _=ε^2*(L^(4*a))^2:=by rw [←pow_mul];congr 2;omega
        _=_:=by ring
    rw [heq]
    simpa only [one_mul] using hh
  have he:=log_error_power_budget (2*a) (7*a-3) 1 L (ε^2) (4*K) hL (sq_nonneg ε)
    (by positivity) hlarge (by omega) hcap2
  simp only [pow_one] at he
  have htotal:K*L^(3*a-5)*(L^(2*a)*t+L^(2*a+1)*ε)^2≤
      2*K*(L^(7*a-5)*t^2+L^(7*a-3)*ε^2):=by
    calc
      _≤K*L^(3*a-5)*(2*((L^(2*a)*t)^2+(L^(2*a+1)*ε)^2)):=hmain
      _=2*K*(L^(3*a-5)*(L^(2*a)*t)^2+L^(3*a-5)*(L^(2*a+1)*ε)^2):=by ring
      _=_:=by rw [hp1,hp2]
  nlinarith only [htotal,htail,he]

noncomputable section

theorem eventually_far_inner_log_budget (a b d:ℕ)(β K:ℝ)(ha:12≤a)(hb:25*a≤b)(hd:3≤d)
    (hβ:0<β)(hK:0≤K):
    ∀ᶠ N:ℕ in Filter.atTop,∀z:ℂ,0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      K*Real.log (N:ℝ)^(3*a-5)*
        (Real.log (N:ℝ)^(2*a)*physicalTransfer d z^(effectiveModelRadius a d N β/8-1)+
          Real.log (N:ℝ)^(2*a+1)*graphPaperError a d N (logarithmicRadius β d N) z)^2≤
        1/Real.log (N:ℝ):=by
  filter_upwards [eventually_effective_eighth_tail_log_budget a d (7*a-5) 1 β (4*K) hd hβ (by positivity),
    eventually_paperError_small a b d β ha hb hd hβ,eventually_log_ge_nat (4*K),
    eventually_log_ge_nat 1,Filter.eventually_ge_atTop 1] with N htail herror hlarge hlog hN
  intro z hz hfloor
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let t:=physicalTransfer d z^(effectiveModelRadius a d N β/8-1)
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have ht:0≤t:=pow_nonneg (physicalTransfer_pos d hd z).le _
  have ht1:t≤1:=pow_le_one₀ (physicalTransfer_pos d hd z).le
    (by nlinarith [physicalTransfer_sq_le_half d hd z])
  have hLp:0<L:=by dsimp only[L];linarith
  have hcap:ε*L^(4*a)≤1:=by
    apply (le_div_iff₀ (pow_pos hLp _)).mp
    simpa only [one_div] using herror z hz hfloor
  have ht2:t^2≤t:=by nlinarith
  have htbudget:4*K*L^(7*a-5)*t^2≤1/L:=
    (mul_le_mul_of_nonneg_left ht2 (by positivity)).trans (by simpa only[pow_one] using htail z)
  exact far_inner_log_budget a L ε t K ha hlog hε ht hK hlarge hcap htbudget

end
end LocalLaw
