import LocalLaw.EffectiveLeafWeights

/-! One-sided effective-radius decay absorbs the full omitted-inner charge. -/
namespace LocalLaw

theorem one_sided_omitted_log_budget (a:ℕ)(L ε t k K:ℝ)(ha:2≤a)(hL:1≤L)
    (hε:0≤ε)(ht:0≤t)(hK:0≤K)(hcap:ε*L^(4*a)≤1)
    (htail:L^(4*a)*t^2≤k^4*ε)(hlarge:K*(k^2+1)≤L):
    K*L^(3*a-4)*(t+ε)≤1/L:=by
  let p:=L^(4*a)
  let q:=L^(3*a-4)
  have hLp:0<L:=by linarith
  have hp:0≤p:=pow_nonneg hLp.le _
  have hq:0≤q:=pow_nonneg hLp.le _
  have hsq:(p*t)^2≤(k^2)^2:=by
    calc
      _=p*(p*t^2):=by ring
      _≤p*(k^4*ε):=mul_le_mul_of_nonneg_left htail hp
      _=k^4*(ε*p):=by ring
      _≤k^4*1:=mul_le_mul_of_nonneg_left hcap (by positivity : 0≤k^4)
      _=_:=by ring
  have hpt:p*t≤k^2:=by nlinarith [mul_nonneg hp ht,sq_nonneg k]
  have hpower:q*L*L≤p:=by
    change L^(3*a-4)*L*L≤L^(4*a)
    rw [←pow_succ,←pow_succ]
    exact pow_le_pow_right₀ hL (by omega)
  have hscaled:(K*q*(t+ε))*L*L≤L:=by
    calc
      _=K*(q*L*L)*(t+ε):=by ring
      _≤K*p*(t+ε):=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpower hK) (add_nonneg ht hε)
      _=K*(p*t+ε*p):=by ring
      _≤K*(k^2+1):=mul_le_mul_of_nonneg_left (add_le_add hpt hcap) hK
      _≤L:=hlarge
  apply (le_div_iff₀ hLp).mpr
  exact (mul_le_mul_right hLp).mp (by simpa only [one_mul] using hscaled)

end LocalLaw
