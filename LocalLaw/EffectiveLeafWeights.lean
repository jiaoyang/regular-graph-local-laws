import LocalLaw.EffectiveModelRadius

/-! # Actual polynomial leaf counts at the shorter radius

Squaring the count uses precisely the four-a powers left in the nominal
localization floor. No altered inflated-error branch is compared.
-/

open Filter
noncomputable section
namespace LocalLaw

theorem effective_leaf_count_half_tail (a d N : ℕ) (β K n : ℝ) (hd : 3≤d)
    (hlog : 1≤Real.log (N:ℝ)) (hK : 0≤K) (hn : 0≤n)
    (hcount : n≤K*Real.log (N:ℝ)^(2*a))
    (hroom : modelRadiusLoss a d N≤logarithmicRadius β d N)
    (z : ℂ) (hz : 0≤z.im)
    (hcap : graphPaperError a d N (logarithmicRadius β d N) z*Real.log (N:ℝ)^4≤1)
    (hlarge : K^2*(((d-1:ℕ):ℝ)^4)≤Real.log (N:ℝ)^4) :
    n*physicalTransfer d z^(effectiveModelRadius a d N β)≤1 := by
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let t:=physicalTransfer d z^(effectiveModelRadius a d N β)
  let k:ℝ:=((d-1:ℕ):ℝ)
  have hLp:0<L:=by dsimp only [L]; linarith
  have hε:0≤ε:=by
    apply graphPaperError_nonnegative a d N _ z _ hz
    by_contra hnN
    have he:N=0:=by omega
    subst N
    norm_num at hlog
  have ht:0≤t:=pow_nonneg (physicalTransfer_pos d hd z).le _
  have htail:L^(4*a)*t^2≤k^4*ε:=by
    have hh:=effectiveModelRadius_localization_tail a d N β hd hlog hroom z hz
    have hp:physicalTransfer d z^(2*effectiveModelRadius a d N β)=t^2:=by
      dsimp only [t]
      rw [mul_comm 2, pow_mul]
    rw [hp] at hh
    have he:=(le_div_iff₀ (pow_pos hLp (4*a))).mp hh
    dsimp only [L,ε,k] at *
    nlinarith only [he]
  have hcountsq:n^2≤K^2*L^(4*a):=by
    have hh:=pow_le_pow_left₀ hn hcount 2
    have he:(K*L^(2*a))^2=K^2*L^(4*a):=by
      rw [mul_pow,←pow_mul]
      congr 2
      omega
    exact hh.trans_eq he
  have htotal:(n*t)^2≤1:=by
    calc
      _=n^2*t^2:=mul_pow n t 2
      _≤(K^2*L^(4*a))*t^2:=mul_le_mul_of_nonneg_right hcountsq (sq_nonneg t)
      _=K^2*(L^(4*a)*t^2):=by ring
      _≤K^2*(k^4*ε):=mul_le_mul_of_nonneg_left htail (sq_nonneg K)
      _=(K^2*k^4)*ε:=by ring
      _≤L^4*ε:=mul_le_mul_of_nonneg_right hlarge hε
      _≤1:=by simpa only [L,ε,mul_comm] using hcap
  nlinarith [mul_nonneg hn ht]

theorem eventually_effective_leaf_count_half_tail (a d : ℕ) (β K : ℝ)
    (hd : 3≤d) (hK : 0≤K) :
    ∀ᶠ N:ℕ in atTop, ∀z:ℂ,0≤z.im→
      modelRadiusLoss a d N≤logarithmicRadius β d N→
      graphPaperError a d N (logarithmicRadius β d N) z*Real.log (N:ℝ)^4≤1→
      ∀n:ℝ,0≤n→n≤K*Real.log (N:ℝ)^(2*a)→
      n*physicalTransfer d z^(effectiveModelRadius a d N β)≤1 := by
  filter_upwards [eventually_log_ge_nat 1,eventually_log_ge_nat (K^2*(((d-1:ℕ):ℝ)^4))]
    with N hlog hlarge
  intro z hz hroom hcap n hn hcount
  apply effective_leaf_count_half_tail a d N β K n hd hlog hK hn hcount hroom z hz hcap
  exact hlarge.trans (by simpa only [pow_one] using pow_le_pow_right₀ hlog (by omega:1≤4))

end LocalLaw
