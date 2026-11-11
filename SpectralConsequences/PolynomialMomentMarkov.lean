import SpectralConsequences.FluctuationMomentBootstrap
import LocalLaw.ParameterGrowth

/-! Fixed high moments with fixed logarithmic losses give every polynomial
tail after an arbitrarily small positive power enlargement. -/
open scoped BigOperators
open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance polynomialMomentMarkovDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem polynomial_moment_order (e:ℝ)(he:0<e)(D:ℕ):
    ∃p:ℕ,2≤p ∧(D:ℝ)≤(p:ℝ)*e:=by
  obtain ⟨n,hn⟩:=exists_nat_ge ((D:ℝ)/e)
  refine ⟨n+2,by omega,?_⟩
  have hh:((D:ℝ))≤(n:ℝ)*e:=(div_le_iff₀ he).mp hn
  push_cast
  nlinarith

theorem polynomial_moment_markov {Ω:Type*}[Fintype Ω](w:Ω→ℝ)(hw:∀ω,0≤w ω)
    (A:Ω→Prop)(F:Ω→ℂ)(N p D:ℕ)(hN:0<N)(e scale:ℝ)(hs:0<scale)
    (hD:(D:ℝ)≤(p:ℝ)*e)
    (hM:truncatedMoment w A F p≤((N:ℝ)^(e/2)*scale)^(2*p)):
    eventMass w (fun ω=>A ω ∧(N:ℝ)^e*scale < ‖F ω‖)≤1/(N:ℝ)^D:=by
  have hNp:0<(N:ℝ):=Nat.cast_pos.mpr hN
  have ht:0<(N:ℝ)^e*scale:=mul_pos (Real.rpow_pos_of_pos hNp _) hs
  have hmp:=truncated_moment_markov w hw A F p ((N:ℝ)^e*scale) ht
  have hbound:eventMass w (fun ω=>A ω ∧(N:ℝ)^e*scale < ‖F ω‖)≤
      ((N:ℝ)^(e/2)*scale)^(2*p)/((N:ℝ)^e*scale)^(2*p):=
    (le_div_iff₀ (pow_pos ht _)).mpr (hmp.trans hM)
  have hratio:((N:ℝ)^(e/2)*scale)^(2*p)/((N:ℝ)^e*scale)^(2*p)=
      (N:ℝ)^(-(p:ℝ)*e):=by
    rw [←div_pow,mul_div_mul_right _ _ (ne_of_gt hs),←Real.rpow_sub hNp]
    rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]
    congr 1
    push_cast
    ring
  rw [hratio] at hbound
  apply hbound.trans
  rw [one_div,←Real.rpow_natCast,←Real.rpow_neg hNp.le]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega)) (by linarith)

theorem eventually_polylog_moment_markov (C b e:ℝ)(hC:0≤C)(he:0<e)
    (p D:ℕ)(hD:(D:ℝ)≤(p:ℝ)*e):
    ∀ᶠ N:ℕ in atTop,∀{Ω:Type*}[Fintype Ω](w:Ω→ℝ)(_hw:∀ω,0≤w ω)
      (A:Ω→Prop)(F:Ω→ℂ)(scale:ℝ),0<scale→
      truncatedMoment w A F p≤(C*Real.log (N:ℝ)^b*scale)^(2*p)→
      eventMass w (fun ω=>A ω ∧(N:ℝ)^e*scale < ‖F ω‖)≤1/(N:ℝ)^D:=by
  filter_upwards [eventually_const_mul_log_rpow_le C b (e/2) (by positivity),
    eventually_log_ge_nat 1,eventually_ge_atTop 1] with N hlog hL hN
  intro Ω _ w hw A F scale hs hM
  apply polynomial_moment_markov w hw A F N p D (by omega) e scale hs hD
  apply hM.trans
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_mul_of_nonneg_right hlog hs.le

end SpectralConsequences
