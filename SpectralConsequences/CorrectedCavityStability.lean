import LocalLaw.ScalarRecursion
import LocalLaw.ScalarStability

/-! Corrected scalar stability after subtracting the deterministic cavity pole. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw

/-- Exact linear-plus-quadratic finite-depth residual. -/
theorem cavity_linear_quadratic_identity {m q z:ℂ}
    (hm:m^2+z*m+1=0)(n:ℕ)
    (hden:∀j≤n,cavityDenominator m (q-m) j≠0):
    (1-m^(2*n))*(q-m)=
      cavityDenominator m (q-m) n*(q-cavityIterate z q n)+
        (m*cavitySum m n)*(q-m)^2:=by
  rw [cavity_iterate_exact hm n hden]
  have hD:=hden n le_rfl
  field_simp [hD]
  dsimp only [cavityDenominator]
  ring

/-- A corrected complex linear equation with its nonlinear coefficient absorbed.
The second term is quadratic in the explicit deterministic correction. -/
theorem corrected_scalar_stability (T a δ c e:ℂ)(R:ℝ)(hT:T≠0)
    (hD:‖1-a*δ‖≤3/2)(he:‖e‖≤R)
    (hid:T*δ=(1-a*δ)*(e+c)+a*δ^2)
    (hsmall:‖a‖*(‖δ‖+‖c‖*(1/‖T‖+1))≤‖T‖/2):
    ‖δ-c/T‖≤3*R/‖T‖+
      2*‖a‖*‖c‖^2*(1+‖T‖)/‖T‖^3:=by
  let x:=δ-c/T
  have ht:0<‖T‖:=norm_pos_iff.mpr hT
  have hR:0≤R:=(norm_nonneg e).trans he
  have hcore:T*x=(1-a*δ)*e+
      a*(δ+c*(T⁻¹-1))*x+a*(c/T)*c*(T⁻¹-1):=by
    dsimp only [x]
    field_simp [hT] at hid ⊢
    linear_combination T^2*hid
  have hrecip:‖T⁻¹-1‖≤1/‖T‖+1:=by
    apply (norm_sub_le _ _).trans_eq
    simp only [norm_inv,norm_one,one_div]
  have hcoef:‖a*(δ+c*(T⁻¹-1))‖≤‖T‖/2:=by
    rw [norm_mul]
    apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg a)).trans
    apply (mul_le_mul_of_nonneg_left _ (norm_nonneg a)).trans hsmall
    apply add_le_add_left _ ‖δ‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hrecip (norm_nonneg c)
  have hconst:‖a*(c/T)*c*(T⁻¹-1)‖≤‖a‖*‖c‖^2/‖T‖*(1/‖T‖+1):=by
    simp only [norm_mul,norm_div]
    calc
      ‖a‖*(‖c‖/‖T‖)*‖c‖*‖T⁻¹-1‖≤‖a‖*(‖c‖/‖T‖)*‖c‖*(1/‖T‖+1):=
        mul_le_mul_of_nonneg_left hrecip (by positivity)
      _=_:=by ring
  have hnorm:‖T‖*‖x‖≤3/2*R+‖T‖/2*‖x‖+
      ‖a‖*‖c‖^2/‖T‖*(1/‖T‖+1):=by
    rw [←norm_mul,hcore]
    apply (norm_add_le _ _).trans
    apply add_le_add (norm_add_le _ _) le_rfl |>.trans
    apply add_le_add _ hconst
    apply add_le_add
    · rw [norm_mul]
      exact mul_le_mul hD he (norm_nonneg e) (by norm_num)
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg x)
  change ‖x‖≤_
  apply (mul_le_mul_right ht).mp
  have htarget:(3*R/‖T‖+2*‖a‖*‖c‖^2*(1+‖T‖)/‖T‖^3)*‖T‖=
      3*R+2*(‖a‖*‖c‖^2/‖T‖*(1/‖T‖+1)):=by
    field_simp
    ring
  rw [htarget]
  linarith

/-- The previous criterion applied to the genuine finite cavity recursion. -/
theorem corrected_cavity_stability {m q z:ℂ}(hm:m^2+z*m+1=0)
    (hmnorm:‖m‖≤1)(n:ℕ)(hprior:(n:ℝ)*‖q-m‖≤1/2)(c:ℂ)(R:ℝ)
    (hT:1-m^(2*n)≠0)(hres:‖q-cavityIterate z q n-c‖≤R)
    (hsmall:‖m*cavitySum m n‖*(‖q-m‖+‖c‖*(1/‖1-m^(2*n)‖+1))≤‖1-m^(2*n)‖/2):
    ‖q-m-c/(1-m^(2*n))‖≤3*R/‖1-m^(2*n)‖+
      2*‖m*cavitySum m n‖*‖c‖^2*(1+‖1-m^(2*n)‖)/‖1-m^(2*n)‖^3:=by
  apply corrected_scalar_stability _ _ _ _ _ _ hT
    (cavityDenominator_bounds hmnorm n hprior).2 hres
  · have hh:=cavity_linear_quadratic_identity hm n (cavityDenominator_all_ne_zero hmnorm n hprior)
    simpa only [sub_add_cancel,cavityDenominator] using hh
  · exact hsmall

end SpectralConsequences
#print axioms SpectralConsequences.corrected_cavity_stability
