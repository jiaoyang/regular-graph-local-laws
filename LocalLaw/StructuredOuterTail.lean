import LocalLaw.StructuredOuterSquare

/-! The distant deletion count is charged only to the spatial tail. -/
namespace LocalLaw

theorem structured_outer_tail (n C A D mass L ε t Z T:ℝ)
    (hn:0≤n)(hC:0≤C)(hmass:0≤ mass)(hL:1≤L)(hε:0≤ε)
    (_hZ:0≤Z)(_hT:0≤T)(hcount:n≤ mass)(hsmall:n*L*ε≤1)(ht:t^2≤Z*T) :
    n*C*(A*L*t+D*L*ε)^2≤
      2*C*D^2*L*ε+2*C*A^2*Z*(mass+1)*L^4*T := by
  have hL0:0≤L:=by linarith
  have hn':n≤ mass+1:=by linarith
  have hpow:L^2≤L^4:=pow_le_pow_right₀ hL (by omega)
  have htail:n*L^2*t^2≤Z*(mass+1)*L^4*T:=by
    calc
      _≤(mass+1)*L^4*(Z*T):=by gcongr
      _=Z*(mass+1)*L^4*T:=by ring
  have htail':2*C*A^2*n*L^2*t^2≤2*C*A^2*Z*(mass+1)*L^4*T:=by
    have hh:=mul_le_mul_of_nonneg_left htail (show 0≤2*C*A^2 by positivity)
    nlinarith only [hh]
  exact (structured_outer_square n C A D L ε t hn hC hL0 hε hsmall).trans
    (add_le_add_left htail' _)

end LocalLaw
