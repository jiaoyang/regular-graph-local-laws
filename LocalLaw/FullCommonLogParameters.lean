import LocalLaw.SharpParameterSmallness

/-! Loose full-Green comparison tolerances from sharp nominal smallness. -/
namespace LocalLaw

theorem full_common_log_budgets (a : ℕ) (L ε n C U M w H : ℝ)
    (ha : 2≤a) (hL : 1≤L) (hε : 0≤ε) (hC : 0≤C)
    (hU : 0≤U) (hM : 0≤M) (hw : 0≤w) (hH : 1≤H)
    (hcount : n≤U*L^(2*a-4)) (hrow : C≤M*L^(2*a-2))
    (hcontract : 4*U*(1+M*w)*w≤H) (herror : 4*(1+M*w)^2≤H)
    (hsharp : ε*L^(4*a+1)≤H⁻¹) :
    n*(1+C*w)*w*(2*L^3*ε)≤1/2 ∧ 4*(1+C*w)^2*L^3*ε≤1/L := by
  have hL0 : 0≤L := by linarith
  have hPa : 1≤L^(2*a-2) := one_le_pow₀ hL
  have hcoeff : 1+C*w≤(1+M*w)*L^(2*a-2) := by
    have hh:=mul_le_mul_of_nonneg_right hrow hw
    nlinarith only [hh,hPa]
  have hp1 : L^(2*a-4)*L^(2*a-2)*L^3≤L^(4*a+1) := by
    rw [←pow_add,←pow_add]
    exact pow_le_pow_right₀ hL (by omega)
  have hp2 : (L^(2*a-2))^2*L^3*L≤L^(4*a+1) := by
    rw [←pow_mul,←pow_add,←pow_succ]
    exact pow_le_pow_right₀ hL (by omega)
  have hεp : 0≤ε*L^(4*a+1) := by positivity
  have hscaled : H*(ε*L^(4*a+1))≤1 := by
    have hh:=mul_le_mul_of_nonneg_left hsharp (show 0≤H by linarith)
    simpa only [mul_inv_cancel₀ (show H≠0 by linarith)] using hh
  have hc : n*(1+C*w)*w*(2*L^3*ε)≤(2*U*(1+M*w)*w)*(ε*L^(4*a+1)) := by
    calc
      _ ≤ (U*L^(2*a-4))*((1+M*w)*L^(2*a-2))*w*(2*L^3*ε) := by gcongr
      _ = (2*U*(1+M*w)*w*ε)*(L^(2*a-4)*L^(2*a-2)*L^3) := by ring
      _ ≤ (2*U*(1+M*w)*w*ε)*L^(4*a+1) := mul_le_mul_of_nonneg_left hp1 (by positivity)
      _ = _ := by ring
  have he : (4*(1+C*w)^2*L^3*ε)*L≤(4*(1+M*w)^2)*(ε*L^(4*a+1)) := by
    calc
      _ ≤ (4*((1+M*w)*L^(2*a-2))^2*L^3*ε)*L := by gcongr
      _ = (4*(1+M*w)^2*ε)*((L^(2*a-2))^2*L^3*L) := by ring
      _ ≤ (4*(1+M*w)^2*ε)*L^(4*a+1) := mul_le_mul_of_nonneg_left hp2 (by positivity)
      _ = _ := by ring
  have hc':=(mul_le_mul_of_nonneg_right hcontract hεp).trans hscaled
  have he':=(mul_le_mul_of_nonneg_right herror hεp).trans hscaled
  refine ⟨by nlinarith only [hc,hc'],?_⟩
  exact (le_div_iff₀ (by linarith : 0<L)).mpr (he.trans he')

end LocalLaw
