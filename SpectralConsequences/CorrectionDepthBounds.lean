import LocalLaw.ClosureParameters
import LocalLaw.ResamplingRadiusGrowth

/-! Literal log-log depth growth and the source height bound control the
numerators of both deterministic corrections uniformly in the spectral point. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem doubleLogRadius_same_base_bound (a d N:ℕ)(hd:3≤d)(hL:1≤Real.log (N:ℝ)):
    (((d-1:ℕ):ℝ)^doubleLogRadius a d N)≤Real.log (N:ℝ)^(2*a):=by
  let k:ℝ:=((d-1:ℕ):ℝ)
  let L:=Real.log (N:ℝ)
  have hk:1<k:=by dsimp only [k];exact_mod_cast (show 1<d-1 by omega)
  have hkp:0<k:=by linarith
  have hlogk:0<Real.log k:=Real.log_pos hk
  have hLp:0<L:=by dsimp only [L];linarith
  have hx:0≤((2*a:ℕ):ℝ)*Real.log L/Real.log k:=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hL)) hlogk.le
  have hfloor:=Nat.floor_le hx
  change (doubleLogRadius a d N:ℝ)≤_ at hfloor
  have hp:=Real.rpow_le_rpow_of_exponent_le hk.le hfloor
  have hid:k^(((2*a:ℕ):ℝ)*Real.log L/Real.log k)=L^((2*a:ℕ):ℝ):=by
    rw [Real.rpow_def_of_pos hkp,Real.rpow_def_of_pos hLp]
    congr 1
    field_simp
    ring
  simpa only [Real.rpow_natCast,hid] using hp

def uniformCorrectionConstant (d:ℕ):ℝ:=32*((d:ℝ)+1)*((d-1:ℕ):ℝ)

theorem eventually_correction_numerator_height (a b d:ℕ)(ha:12≤a)(hb:25*a≤b)(hd:3≤d):
    ∀ᶠ N:ℕ in Filter.atTop,∀z:ℂ,0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      uniformCorrectionConstant d*((d-1:ℕ):ℝ)^(actualCavityDepth a d N z-1)≤(N:ℝ)*z.im:=by
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_log_ge_nat (max 1 (uniformCorrectionConstant d)),hdepth,
    Filter.eventually_ge_atTop 1] with N hL hdepth hN
  intro z _ hfloor
  let L:=Real.log (N:ℝ)
  let C:=uniformCorrectionConstant d
  let k:ℝ:=((d-1:ℕ):ℝ)
  let ell:=actualCavityDepth a d N z-1
  have hL1:1≤L:=(le_max_left _ _).trans hL
  have hC:C≤L:=(le_max_right _ _).trans hL
  have hC0:0≤C:=by dsimp only [C,uniformCorrectionConstant];positivity
  have hk:1≤k:=by dsimp only [k];exact_mod_cast (show 1≤d-1 by omega)
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepth).2
  have hpow:k^ell≤L^(2*a):=(pow_le_pow_right₀ hk hell).trans
    (doubleLogRadius_same_base_bound a d N hd hL1)
  have hgap:1≤b-2*a:=by omega
  have hCb:C≤L^(b-2*a):=hC.trans (by simpa only [pow_one] using pow_le_pow_right₀ hL1 hgap)
  have hbudget:C*k^ell≤L^b:=by
    calc
      _≤L^(b-2*a)*L^(2*a):=mul_le_mul hCb hpow (by positivity) (by positivity)
      _=L^b:=by rw [←pow_add];congr 1;omega
  have hNp:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  have hh:Real.log (N:ℝ)^b≤z.im*(N:ℝ):=(div_le_iff₀ hNp).mp hfloor
  exact hbudget.trans (by simpa only [mul_comm] using hh)

end SpectralConsequences
