import SpectralConsequences.RootParameterContinuity
import LocalLaw.ParameterSmallness
import LocalLaw.ClosureParameters

/-! The small displacement conditions for both recursion targets hold
uniformly throughout the source spectral domain. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem eventually_source_recursion_smallness (a b d:ℕ)(β:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hβ:0<β):
    ∀ᶠ N:ℕ in Filter.atTop,∀z:ℂ,0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      let ell:=actualCavityDepth a d N z-1
      ((ell:ℝ)+4)*scalarScale (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z)≤1/2:=by
  filter_upwards [eventually_paperError_small a b d β ha hb hd hβ,
    eventually_actualCavityDepth_le_log a d hd,eventually_log_ge_nat 4,
    Filter.eventually_ge_atTop 1] with N herror hdepth hL hN
  intro z hz hfloor
  dsimp only
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  have hLp:0<L:=by dsimp only [L];linarith
  have hL1:1≤L:=by dsimp only [L];linarith
  have hε:0≤ε:=graphPaperError_nonnegative _ _ _ _ _ hN hz.le
  have hpow:L^4≤L^(4*a):=pow_le_pow_right₀ hL1 (by omega)
  have hε4:ε≤1/L^4:=by
    have hh:=herror z hz hfloor
    change ε≤(L^(4*a))⁻¹ at hh
    exact hh.trans (by simpa only [one_div] using inv_anti₀ (pow_pos hLp 4) hpow)
  have hΨ:scalarScale (spectralScale z) ε≤1/L^2:=by
    apply (scalarScale_le_sqrt (spectralScale_pos hz) hε).trans
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,hε4.trans_eq ?_⟩
    rw [div_pow,one_pow,←pow_mul]
  have hell:((actualCavityDepth a d N z-1:ℕ):ℝ)≤L:=
    (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (hdepth z)
  calc
    _≤(L+4)*(1/L^2):=mul_le_mul (by linarith) hΨ (scalarScale_nonneg hε) (by positivity)
    _≤1/2:=by
      rw [mul_one_div]
      apply (div_le_iff₀ (pow_pos hLp 2)).mpr
      have hL4:4≤L:=hL
      nlinarith [sq_nonneg (L-4)]

end SpectralConsequences
