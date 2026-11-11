import SpectralConsequences.TrivialCavityCap
import SpectralConsequences.RegularRootTaylor

/-! A global explicit cap on the actual trace correction. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem trivialTraceCorrection_norm_le (N d ell:ℕ)(hN:1≤N)(hd:3≤d)(z:ℂ)(hz:0<z.im):
    ‖trivialTraceCorrection N d ell z‖≤
      32*((d:ℝ)+1)*((d-1:ℕ):ℝ)^ell/((N:ℝ)*z.im):=by
  let m:=semicircleRoot z
  let md:=kestenMcKayTransform d m z
  let K:=((d-1:ℕ):ℝ)^ell
  have hK:1≤K:=one_le_pow₀ (by exact_mod_cast (show 1≤d-1 by omega))
  have hm:‖m‖≤1:=semicircleRoot_norm_le_one z
  have hα:‖treeEdgeWeight d‖≤1:=(treeEdgeWeight_norm_le_three_quarters d hd).trans (by norm_num)
  have hfactor:‖1+m*treeEdgeWeight d‖≤2:=by
    apply (norm_add_le _ _).trans
    simp only [norm_one,norm_mul]
    have hh:=mul_le_mul hm hα (norm_nonneg _) (by norm_num)
    linarith
  have hfirst:‖(d:ℂ)*((d-1:ℕ):ℂ)^ell-1‖≤((d:ℝ)+1)*K:=by
    have hh:=norm_sub_le ((d:ℂ)*((d-1:ℕ):ℂ)^ell) (1:ℂ)
    simp only [norm_mul,norm_pow,Complex.norm_natCast,norm_one] at hh
    change ‖(d:ℂ)*((d-1:ℕ):ℂ)^ell-1‖≤((d:ℝ)+1)*K
    change ‖(d:ℂ)*((d-1:ℕ):ℂ)^ell-1‖≤(d:ℝ)*K+1 at hh
    nlinarith
  have hcoeff:‖traceCorrectionCoefficient d ell m md‖≤32*((d:ℝ)+1)*K:=by
    have heq:traceCorrectionCoefficient d ell m md=
        regularRootLinearCoefficient d ell m md*((d:ℂ)*((d-1:ℕ):ℂ)^ell-1)*
          (1+m*treeEdgeWeight d)^2:=by
      unfold traceCorrectionCoefficient regularRootLinearCoefficient
      ring
    rw [heq,norm_mul,norm_mul,norm_pow]
    have hs:‖1+m*treeEdgeWeight d‖^2≤4:=by nlinarith [norm_nonneg (1+m*treeEdgeWeight d)]
    have hh:=mul_le_mul (mul_le_mul (regularRootLinearCoefficient_norm_le_eight d ell hd z hz)
      hfirst (norm_nonneg _) (by norm_num)) hs (sq_nonneg _) (by positivity)
    exact hh.trans_eq (by ring)
  unfold trivialTraceCorrection
  rw [norm_mul]
  have hh:=mul_le_mul hcoeff (trivialPole_norm_le N d hN z hz) (norm_nonneg _) (by positivity)
  exact hh.trans_eq (by ring)

end SpectralConsequences
