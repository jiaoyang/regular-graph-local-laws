import LocalLaw.ScalarRecursion

/-! # Boundary-parameter continuity of the genuine finite cavity iteration -/

namespace LocalLaw

theorem cavityIterate_lipschitz_of_small {m z u v : ℂ}
    (hm : m^2+z*m+1=0) (hmnorm : ‖m‖≤1) (n : ℕ)
    (hu : (n:ℝ)*‖u-m‖≤1/2) (hv : (n:ℝ)*‖v-m‖≤1/2) :
    ‖cavityIterate z u n-cavityIterate z v n‖≤4*‖u-v‖ := by
  let Du := cavityDenominator m (u-m) n
  let Dv := cavityDenominator m (v-m) n
  have hDu : Du≠0 := cavityDenominator_ne_zero hmnorm n hu
  have hDv : Dv≠0 := cavityDenominator_ne_zero hmnorm n hv
  have hformula : cavityIterate z u n-cavityIterate z v n=m^(2*n)*(u-v)/(Du*Dv) := by
    rw [cavity_iterate_exact_of_small hm hmnorm n hu,cavity_iterate_exact_of_small hm hmnorm n hv]
    change (m+m^(2*n)*(u-m)/Du)-(m+m^(2*n)*(v-m)/Dv)=_
    field_simp [hDu,hDv]
    dsimp only [Du,Dv,cavityDenominator]
    ring
  have hlu : 1/2≤‖Du‖ := (cavityDenominator_bounds hmnorm n hu).1
  have hlv : 1/2≤‖Dv‖ := (cavityDenominator_bounds hmnorm n hv).1
  have hden : 1/4≤‖Du‖*‖Dv‖ := by nlinarith only [hlu,hlv]
  have hdenpos : 0<‖Du‖*‖Dv‖ := by linarith
  have hpow : ‖m‖^(2*n)≤1 := pow_le_one₀ (norm_nonneg _) hmnorm
  rw [hformula,norm_div,norm_mul,norm_mul,norm_pow]
  apply (div_le_iff₀ hdenpos).mpr
  have hnum := mul_le_mul_of_nonneg_right hpow (norm_nonneg (u-v))
  have hmult := mul_le_mul_of_nonneg_left hden (norm_nonneg (u-v))
  nlinarith only [hnum,hmult]

end LocalLaw
