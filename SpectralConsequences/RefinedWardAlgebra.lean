import LocalLaw.SwitchingQParameters

/-! Folding the genuine Ward and changed-edge terms into one variance. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw

def refinedWardCoefficient (C P H K:ℝ):ℝ:=8*((1+C*P)^2*K+H*(C+C^2*P))+8*K+1

theorem refined_ward_budgets (N:ℕ)(d:ℕ)(μ C P H K I J η:ℝ)
    (hN:0<N)(hd:3≤d)(hμ:0≤μ)(hC:0≤C)(hP:0≤P)(hH:0≤H)(hK:0≤K)
    (hI:0≤I)(hJ:0≤J)(hη:0<η)(hheight:η≤H*J)(hIJ:I≤K*J):
    ((N:ℝ)*(d:ℝ))⁻¹*
      (((d:ℝ)*(1+C*P)^2*I/η)*(8*μ/Real.sqrt ((d:ℝ)-1))+8*μ*(C+C^2*P))≤
      refinedWardCoefficient C P H K*μ*J/((N:ℝ)*η) ∧
    (N:ℝ)⁻¹*(I/η)*(8*μ/Real.sqrt ((d:ℝ)-1))≤
      refinedWardCoefficient C P H K*μ*J/((N:ℝ)*η):=by
  have hn:0<(N:ℝ):=Nat.cast_pos.mpr hN
  have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
  have hdpos:0<(d:ℝ):=by linarith
  have hsqrt:1≤Real.sqrt ((d:ℝ)-1):=Real.one_le_sqrt.mpr (by linarith)
  have hμdiv:8*μ/Real.sqrt ((d:ℝ)-1)≤8*μ:=div_le_self (by positivity) hsqrt
  have hsmall:(C+C^2*P)/(d:ℝ)≤H*J*(C+C^2*P)/η:=by
    apply (div_le_self (by positivity:0≤C+C^2*P) (by linarith:(1:ℝ)≤d)).trans
    apply (le_div_iff₀ hη).mpr
    nlinarith [mul_le_mul_of_nonneg_right hheight (show 0≤C+C^2*P by positivity)]
  have hcoef:0≤refinedWardCoefficient C P H K:=by dsimp only [refinedWardCoefficient];positivity
  constructor
  · calc
      _≤((N:ℝ)*(d:ℝ))⁻¹*((d:ℝ)*(1+C*P)^2*I/η*(8*μ)+8*μ*(C+C^2*P)):=by gcongr
      _=8*μ/(N:ℝ)*((1+C*P)^2*I/η+(C+C^2*P)/(d:ℝ)):=by field_simp;ring
      _≤8*μ/(N:ℝ)*((1+C*P)^2*(K*J)/η+H*J*(C+C^2*P)/η):=by
        exact mul_le_mul_of_nonneg_left (add_le_add
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hIJ (sq_nonneg _)) hη.le) hsmall) (by positivity)
      _=(8*((1+C*P)^2*K+H*(C+C^2*P)))*μ*J/((N:ℝ)*η):=by field_simp;ring
      _≤_:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp only [refinedWardCoefficient];linarith) hμ) hJ) (by positivity)
  · calc
      _≤(N:ℝ)⁻¹*(I/η)*(8*μ):=mul_le_mul_of_nonneg_left hμdiv (by positivity)
      _≤(N:ℝ)⁻¹*((K*J)/η)*(8*μ):=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hIJ hη.le) (by positivity)) (by positivity)
      _=(8*K)*μ*J/((N:ℝ)*η):=by field_simp;ring
      _≤_:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (by
          have hh:0≤8*((1+C*P)^2*K+H*(C+C^2*P)):=by positivity
          dsimp only [refinedWardCoefficient]
          linarith) hμ) hJ) (by positivity)

end SpectralConsequences
#print axioms SpectralConsequences.refined_ward_budgets
