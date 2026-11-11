import Mathlib

/-! # Distant-vertex deletion retains a first-order weak residual

The true count is confined to the spatial tail. A realized count contraction
removes it from the ordinary error before the full inner-set lift.
-/

namespace LocalLaw

theorem structured_outer_square (n C A D L ε t:ℝ)
    (hn:0≤n)(hC:0≤C)(hL:0≤L)(hε:0≤ε)(hsmall:n*L*ε≤1) :
    n*C*(A*L*t+D*L*ε)^2≤2*C*D^2*L*ε+2*C*A^2*n*L^2*t^2 := by
  have hquad:n*L^2*ε^2≤L*ε:=by
    have hh:=mul_le_mul_of_nonneg_right hsmall (mul_nonneg hL hε)
    nlinarith only [hh]
  have hweak:=mul_le_mul_of_nonneg_left hquad (show 0≤2*C*D^2 by positivity)
  have hsq:(A*L*t+D*L*ε)^2≤2*(A*L*t)^2+2*(D*L*ε)^2:=by
    nlinarith only [sq_nonneg (A*L*t-D*L*ε)]
  have hbound:=mul_le_mul_of_nonneg_left hsq (mul_nonneg hn hC)
  nlinarith only [hweak,hbound]

theorem count_linear_residual_contraction (a:ℕ)(ha:1≤a)(L ε n Count:ℝ)
    (hL:1≤L)(hε:0≤ε)(_hCount:0≤Count)
    (hcount:n≤Count*L^(2*a))(hcap:ε*L^(4*a)≤1)(hlarge:Count≤L) :
    n*L*ε≤1 := by
  have hL0:0≤L:=by linarith
  calc
    _≤(Count*L^(2*a))*L*ε:=by gcongr
    _=Count*L^(2*a+1)*ε:=by rw [pow_add,pow_one];ring
    _≤L*L^(2*a+1)*ε:=by gcongr
    _=L^(2*a+2)*ε:=by rw [pow_succ];ring
    _≤L^(4*a)*ε:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (by omega)) hε
    _≤1:=by nlinarith only [hcap]

end LocalLaw
