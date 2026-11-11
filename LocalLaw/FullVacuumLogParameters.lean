import LocalLaw.SharpParameterSmallness

/-! # Full vacuum row contraction with the actual selected-depth gain -/

namespace LocalLaw

theorem full_vacuum_log_budgets (a : ℕ) (L ε n C U M w D H : ℝ)
    (ha : 2 ≤ a) (hL : 1 ≤ L) (hε : 0 ≤ ε) (_hn : 0 ≤ n) (hC : 0 ≤ C)
    (hU : 0 ≤ U) (hM : 0 ≤ M) (hw : 0 ≤ w) (hD : 0 ≤ D) (hH : 1 ≤ H)
    (hcount : n ≤ U*L^(2*a-4)) (hrow : C ≤ M*L^(a-1))
    (hcontract : 2*U*(1+M*w)*w*D ≤ H) (herror : 2*U*(1+M*w)^2*D ≤ H)
    (hsharp : ε*L^(4*a+1) ≤ H⁻¹) :
    n*(1+C*w)*w*(D*L*ε)≤1/2 ∧ n*(2*(1+C*w)^2*(D*L*ε))≤1 := by
  have hL0 : 0 ≤ L := by linarith
  have hPa : 1 ≤ L^(a-1) := one_le_pow₀ hL
  have hcoeff : 1+C*w ≤ (1+M*w)*L^(a-1) := by
    have hh := mul_le_mul_of_nonneg_right hrow hw
    nlinarith only [hh,hPa]
  have hp1 : L^(2*a-4)*L^(a-1)*L ≤ L^(4*a+1) := by
    rw [←pow_add,←pow_succ]
    exact pow_le_pow_right₀ hL (by omega)
  have hp2 : L^(2*a-4)*(L^(a-1))^2*L ≤ L^(4*a+1) := by
    rw [←pow_mul,←pow_add,←pow_succ]
    exact pow_le_pow_right₀ hL (by omega)
  have hεpow : 0 ≤ ε*L^(4*a+1) := by positivity
  have hscaled : H*(ε*L^(4*a+1))≤1 := by
    have hh := mul_le_mul_of_nonneg_left hsharp (show 0≤H by linarith)
    simpa only [mul_inv_cancel₀ (show H≠0 by linarith)] using hh
  have hc : n*(1+C*w)*w*(D*L*ε)≤(U*(1+M*w)*w*D)*(ε*L^(4*a+1)) := by
    calc
      _ ≤ (U*L^(2*a-4))*((1+M*w)*L^(a-1))*w*(D*L*ε) := by gcongr
      _ = (U*(1+M*w)*w*D*ε)*(L^(2*a-4)*L^(a-1)*L) := by ring
      _ ≤ (U*(1+M*w)*w*D*ε)*L^(4*a+1) := mul_le_mul_of_nonneg_left hp1 (by positivity)
      _ = _ := by ring
  have he : n*(2*(1+C*w)^2*(D*L*ε))≤(2*U*(1+M*w)^2*D)*(ε*L^(4*a+1)) := by
    calc
      _ ≤ (U*L^(2*a-4))*(2*((1+M*w)*L^(a-1))^2*(D*L*ε)) := by gcongr
      _ = (2*U*(1+M*w)^2*D*ε)*(L^(2*a-4)*(L^(a-1))^2*L) := by ring
      _ ≤ (2*U*(1+M*w)^2*D*ε)*L^(4*a+1) := mul_le_mul_of_nonneg_left hp2 (by positivity)
      _ = _ := by ring
  have hc' := (mul_le_mul_of_nonneg_right hcontract hεpow).trans hscaled
  have he' := (mul_le_mul_of_nonneg_right herror hεpow).trans hscaled
  exact ⟨by nlinarith only [hc,hc'],he.trans he'⟩

end LocalLaw
