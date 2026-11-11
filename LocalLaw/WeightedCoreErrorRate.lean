import LocalLaw.WeightedAsymmetricCoreError

/-! # The restored finite-star error is a fixed multiple of epsilon-prime -/

namespace LocalLaw

theorem weighted_core_error_to_prime (m n K U V C L ε ρ:ℝ)(r:ℕ)
    (hL:1≤L)(hε:0≤ε)(hεone:ε≤1)(hn:0≤n)(hK:0≤K)(hU:0≤U)(hV:0≤V)(hC:0≤C)(hρ:0≤ρ)
    (htail:V*(n+1)*ρ^(2*r)≤ε/L^16) :
    m^2*((K*L)^2*(U*L*ε)+(K*L)^2*(V*(n+1))*ρ^(2*r)+
      C*(K*L*ε)*(2*(K*L)+K*L*ε))≤
        (m^2*K^2*(U+3*C+1))*(L^3*ε) := by
  have hLp:0<L:=by linarith
  have hL0:0≤L:=hLp.le
  have hL23:L^2≤L^3:=pow_le_pow_right₀ hL (by omega)
  have hεdiv:ε/L^16≤ε:=by
    apply (div_le_iff₀ (pow_pos hLp 16)).mpr
    exact le_mul_of_one_le_right hε (one_le_pow₀ hL)
  have ht:V*(n+1)*ρ^(2*r)≤ε:=htail.trans hεdiv
  have hfirst:(K*L)^2*(U*L*ε)=K^2*U*(L^3*ε):=by ring
  have hsecond:(K*L)^2*(V*(n+1))*ρ^(2*r)≤K^2*(L^3*ε):=by
    have hh:=mul_le_mul_of_nonneg_left ht (sq_nonneg (K*L))
    have hp:=mul_le_mul_of_nonneg_left hL23 (mul_nonneg (sq_nonneg K) hε)
    nlinarith only [hh,hp]
  have hthird:C*(K*L*ε)*(2*(K*L)+K*L*ε)≤3*C*K^2*(L^3*ε):=by
    have hsmall:2*(K*L)+K*L*ε≤3*K*L:=by
      have hh:=mul_le_mul_of_nonneg_left hεone (mul_nonneg hK hL0)
      nlinarith only [hh]
    have hh:=mul_le_mul_of_nonneg_left hsmall (show 0≤C*(K*L*ε) by positivity)
    have hp:=mul_le_mul_of_nonneg_left hL23 (show 0≤3*C*K^2*ε by positivity)
    nlinarith only [hh,hp]
  have hsum:(K*L)^2*(U*L*ε)+(K*L)^2*(V*(n+1))*ρ^(2*r)+
      C*(K*L*ε)*(2*(K*L)+K*L*ε)≤K^2*(U+3*C+1)*(L^3*ε):=by
    rw [hfirst]
    nlinarith only [hsecond,hthird]
  exact (mul_le_mul_of_nonneg_left hsum (sq_nonneg m)).trans_eq (by ring)

end LocalLaw
