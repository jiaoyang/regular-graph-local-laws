import SpectralConsequences.SourceCountingProbability
import SpectralConsequences.KestenMcKayQuantiles
import SpectralConsequences.QuantileRigidity

/-! The final source rigidity event and the genuine counting-to-quantile step.
The confinement event here is subsequently proved by fluctuation averaging. -/
open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceRigidityAssemblyDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def SourceConfinementGood {N d:ℕ}(β:ℝ)(g:RegularGraph N d):Prop:=
  ∀i:Fin N,i.val≠0→
    -2-(N:ℝ)^(-β/16)≤sortedEigenvalues g.H_hermitian i ∧
    sortedEigenvalues g.H_hermitian i≤2+(N:ℝ)^(-β/16)

def SourceRigid {N d:ℕ}(hd:3≤d)(α:ℝ)(g:RegularGraph N d):Prop:=
  ∀i:Fin N,i.val≠0→
    |sortedEigenvalues g.H_hermitian i-classicalLocation d hd i|≤(N:ℝ)^(-α)

theorem eventually_quantile_rate_budget (β:ℝ)(hβ:0<β):
    ∀ᶠ N:ℕ in atTop,
      (N:ℝ)^(-β/16)+((N:ℝ)^(-β/8)/(1/(12*Real.pi)))^(2/3:ℝ)≤
        (N:ℝ)^(-β/32):=by
  let C:ℝ:=(12*Real.pi)^(2/3:ℝ)
  filter_upwards [eventually_const_mul_log_rpow_le (1+C) 0 (β/32) (by positivity),
    eventually_ge_atTop 1] with N hC hN
  have hNp:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  have hN1:1≤(N:ℝ):=Nat.one_le_cast.mpr hN
  have hCp:0≤C:=Real.rpow_nonneg (by positivity) _
  have hC':1+C≤(N:ℝ)^(β/32):=by simpa only [Real.rpow_zero,mul_one] using hC
  have hinside:(N:ℝ)^(-β/8)/(1/(12*Real.pi))=(12*Real.pi)*(N:ℝ)^(-β/8):=by
    rw [one_div,div_inv_eq_mul]
    ring
  have hpow:((N:ℝ)^(-β/8)/(1/(12*Real.pi)))^(2/3:ℝ)=C*(N:ℝ)^(-β/12):=by
    rw [hinside,Real.mul_rpow (by positivity) (by positivity),←Real.rpow_mul hNp.le]
    congr 2
    ring
  rw [hpow]
  have hrate:(N:ℝ)^(-β/12)≤(N:ℝ)^(-β/16):=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  calc
    _≤(1+C)*(N:ℝ)^(-β/16):=by nlinarith
    _≤(N:ℝ)^(β/32)*(N:ℝ)^(-β/16):=
      mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hNp.le _)
    _=_:=by rw [←Real.rpow_add hNp];congr 1;ring

theorem eventually_source_rigid_of_counting_and_confinement (d:ℕ)(hd:3≤d)(β:ℝ)(hβ:0<β):
    ∀ᶠ N:ℕ in atTop,∀g:RegularGraph N d,
      SourceCountingCDFGood β g→SourceConfinementGood β g→SourceRigid hd (β/32) g:=by
  filter_upwards [eventually_quantile_rate_budget β hβ] with N hbudget
  intro g hcount hconf i hi
  have hc:=SquareRootCDF.rigidity_of_cdf_and_confinement (kestenMcKaySquareRootCDF d hd)
    (sortedEigenvalues g.H_hermitian) (sortedEigenvalues_antitone g.H_hermitian)
    ((N:ℝ)^(-β/8)) ((N:ℝ)^(-β/16)) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (Real.rpow_nonneg (Nat.cast_nonneg N) _) hcount i (hconf i hi).1 (hconf i hi).2
  apply hc.trans
  change (N:ℝ)^(-β/16)+((N:ℝ)^(-β/8)/(1/(12*Real.pi)))^(2/3:ℝ)≤(N:ℝ)^(-(β/32))
  simpa only [neg_div] using hbudget

end SpectralConsequences
