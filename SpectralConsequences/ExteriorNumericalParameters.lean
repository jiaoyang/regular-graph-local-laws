import SpectralConsequences.ExteriorError
import SpectralConsequences.ExteriorTraceBudget

/-! # Fixed logarithmic losses fit the exterior correction budget -/
open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw

def exteriorPower (β:ℝ) (N:ℕ):ℝ:=(N:ℝ)^(β/16)
def exteriorLogCap (K:ℝ) (p N:ℕ):ℝ:=K*Real.log (N:ℝ)^p

structure ExteriorNumericalParameters (β γ e K:ℝ) (p N:ℕ) : Prop where
  size_positive : 0<N
  power_one : 1≤exteriorPower β N
  log_cap_one : 1≤exteriorLogCap K p N
  moment_one : 1≤(N:ℝ)^e
  height_identity : (exteriorPower β N)^24=(N:ℝ)*exteriorHeight β N
  size_power : (exteriorPower β N)^26≤(N:ℝ)
  exit_power : (exteriorPower β N)^11≤(N:ℝ)^γ
  first_smallness : 2*(exteriorLogCap K p N)^2≤(exteriorPower β N)^14
  second_smallness : 6*(exteriorLogCap K p N)^4≤(exteriorPower β N)^13
  trace_absorption : 140*(exteriorLogCap K p N)^6*(N:ℝ)^e/exteriorPower β N≤1/16

theorem eventually_exterior_numerical_parameters (β γ e K:ℝ) (p:ℕ)
    (hβ:0<β) (hβsmall:β≤1/128) (hγ:9/32≤γ) (he:0≤e) (heβ:e<β/16) (hK:1≤K):
    ∀ᶠ N:ℕ in atTop,ExteriorNumericalParameters β γ e K p N := by
  filter_upwards [eventually_const_mul_log_rpow_le (6*K^4) ((4*p:ℕ):ℝ) (13*β/16) (by linarith),
    eventually_const_mul_log_rpow_le (2240*K^6) ((6*p:ℕ):ℝ) (β/16-e) (by linarith),
    eventually_log_ge_nat 1,eventually_ge_atTop 1] with N hsmall htrace hL hN
  have hNp:0<(N:ℝ):=by exact_mod_cast (show 0<N by omega)
  have hN1:1≤(N:ℝ):=by exact_mod_cast hN
  let x:=exteriorPower β N
  let H:=exteriorLogCap K p N
  have hx:1≤x:=Real.one_le_rpow hN1 (by linarith)
  have hxp:0<x:=by linarith
  have hH:1≤H:=one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hL)
  have hHp:0<H:=by linarith
  have hV:1≤(N:ℝ)^e:=Real.one_le_rpow hN1 he
  have hxpow (n:ℕ):x^n=(N:ℝ)^((β/16)*n):=by
    dsimp only[x,exteriorPower]
    exact (Real.rpow_mul_natCast hNp.le _ _).symm
  have hsmall':6*H^4≤x^13:=by
    rw [hxpow]
    have hh:6*H^4=6*K^4*Real.log (N:ℝ)^(4*p):=by
      dsimp only[H,exteriorLogCap]
      rw [mul_pow,←pow_mul, Nat.mul_comm p 4]
      ring
    rw [hh]
    convert hsmall using 1
    · rw [Real.rpow_natCast]
    · congr 1
      norm_num
      ring
  have hfirst:2*H^2≤x^14:=by
    have hHpow:H^2≤H^4:=pow_le_pow_right₀ hH (by norm_num)
    have hxpow':x^13≤x^14:=pow_le_pow_right₀ hx (by norm_num)
    nlinarith only[hHpow,hsmall',hxpow',pow_nonneg hHp.le 4]
  have htrace':2240*H^6*(N:ℝ)^e≤x:=by
    have hh:2240*H^6=2240*K^6*Real.log (N:ℝ)^(6*p):=by
      dsimp only[H,exteriorLogCap]
      rw [mul_pow,←pow_mul,Nat.mul_comm p 6]
      ring
    have hr:=mul_le_mul_of_nonneg_right htrace (Real.rpow_nonneg hNp.le e)
    rw [←Real.rpow_add hNp] at hr
    have hex:(β/16-e)+e=β/16:=by ring
    rw [hex] at hr
    rw [hh]
    simpa only[Real.rpow_natCast] using hr
  refine ⟨by omega,hx,hH,hV,?_,?_,?_,hfirst,hsmall',?_⟩
  · rw [hxpow,exterior_height_scale β N (by omega)]
    congr 1
    norm_num
    ring
  · rw [hxpow]
    have hh:=Real.rpow_le_rpow_of_exponent_le hN1 (show (β/16)*(26:ℕ)≤1 by norm_num;linarith only[hβsmall])
    simpa only[Real.rpow_one] using hh
  · rw [hxpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num;linarith only[hβsmall,hγ])
  · apply (div_le_iff₀ hxp).mpr
    nlinarith only[htrace']

end SpectralConsequences
