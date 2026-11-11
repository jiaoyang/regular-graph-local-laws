import LocalLaw.EffectiveTailCounting

/-! # The far sampled-deletion square fits the nominal prime error

The main tail pays the true sample count once. Its weak residual cross term
is bounded by the same elementary square estimate and a realized scalar
contraction, with the nominal error retained throughout.
-/

namespace LocalLaw

theorem far_deletion_square_to_prime (L ε n C A D t:ℝ)
    (hL:2≤L)(hε:0≤ε)(hn:0≤n)(hC:0≤C)(hA:0≤A)(hD:0≤D)(ht:0≤t)
    (htail:(2*C*A^2)*n*t^2≤ε/L^16)
    (hquadratic:(2*C*D^2)*n*L^2*ε≤1) :
    n*C*(A*L*t+D*L*ε)^2≤L^3*ε := by
  have hLp:0<L:=by linarith
  have hLone:1≤L:=by linarith
  have hfirst:(2*C*A^2)*n*L^2*t^2≤ε:=by
    have hh:=mul_le_mul_of_nonneg_right htail (sq_nonneg L)
    have hpow:L^2≤L^16:=pow_le_pow_right₀ hLone (by omega)
    have hratio:ε/L^16*L^2≤ε:=by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (pow_pos hLp 16)).mpr
      exact mul_le_mul_of_nonneg_left hpow hε
    exact (by nlinarith only [hh] : (2*C*A^2)*n*L^2*t^2≤ε/L^16*L^2).trans hratio
  have hsecond:(2*C*D^2)*n*L^2*ε^2≤ε:=by
    have hh:=mul_le_mul_of_nonneg_right hquadratic hε
    nlinarith only [hh]
  have hsq:(A*L*t+D*L*ε)^2≤2*(A*L*t)^2+2*(D*L*ε)^2:=by
    nlinarith only [sq_nonneg (A*L*t-D*L*ε)]
  have hbound:=mul_le_mul_of_nonneg_left hsq (mul_nonneg hn hC)
  have hLcube:2≤L^3:=by nlinarith [pow_le_pow_left₀ (by norm_num:(0:ℝ)≤2) hL 3]
  have hlast:=mul_le_mul_of_nonneg_right hLcube hε
  nlinarith only [hfirst,hsecond,hbound,hlast]

end LocalLaw
