import SpectralConsequences.TrivialCorrections

/-! Polynomial estimates for the uniform trivial-pole cancellation. -/
noncomputable section
namespace SpectralConsequences

theorem unit_disk_power_lipschitz (x y:ℂ)(hx:‖x‖≤1)(hy:‖y‖≤1)(n:ℕ):
    ‖x^n-y^n‖≤(n:ℝ)*‖x-y‖:=by
  induction n with
  | zero=>simp
  | succ n ih=>
    have he:x^(n+1)-y^(n+1)=x*(x^n-y^n)+(x-y)*y^n:=by rw [pow_succ,pow_succ];ring
    rw [he]
    calc
      _≤‖x*(x^n-y^n)‖+‖(x-y)*y^n‖:=norm_add_le _ _
      _=‖x‖*‖x^n-y^n‖+‖x-y‖*‖y‖^n:=by rw [norm_mul,norm_mul,norm_pow]
      _≤1*((n:ℝ)*‖x-y‖)+‖x-y‖*1:=
        add_le_add (mul_le_mul hx ih (norm_nonneg _) (by norm_num))
          (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg y) hy) (norm_nonneg _))
      _=((n+1:ℕ):ℝ)*‖x-y‖:=by push_cast;ring

def correctionPolynomial (a b A u:ℂ):ℂ:=
  a*A-b*A^2-(1-u)^2*(1-A)

theorem correctionPolynomial_pole_zero (k K:ℂ)(hk:k≠0)(hK:K≠0):
    correctionPolynomial ((k+1)/k*((k+1)*K-1)) ((k+1)/k*K)
      (1/(k*K)) (-1/k)=0:=by
  unfold correctionPolynomial
  field_simp [hk,hK]
  ring

theorem correctionPolynomial_lipschitz (a b A A0 u u0:ℂ)
    (hA:‖A‖≤1)(hA0:‖A0‖≤1)(hu:‖u‖≤1)(hu0:‖u0‖≤1):
    ‖correctionPolynomial a b A u-correctionPolynomial a b A0 u0‖≤
      (‖a‖+2*‖b‖+4)*‖A-A0‖+8*‖u-u0‖:=by
  have hs:‖1-u‖≤2:=by have hh:=norm_sub_le (1:ℂ) u;norm_num only [norm_one] at hh;linarith
  have hs0:‖1-u0‖≤2:=by have hh:=norm_sub_le (1:ℂ) u0;norm_num only [norm_one] at hh;linarith
  have htwo:‖2-u-u0‖≤4:=by
    have hh:‖(2:ℂ)-u-u0‖≤‖(2:ℂ)‖+‖u‖+‖u0‖:=(norm_sub_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
    norm_num at hh
    linarith
  have hsq:‖(1-u)^2-(1-u0)^2‖≤4*‖u-u0‖:=by
    rw [show (1-u)^2-(1-u0)^2=(u0-u)*(2-u-u0) by ring,norm_mul,norm_sub_rev]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left htwo (norm_nonneg (u-u0))
  have hprod:‖(1-u)^2*(1-A)-(1-u0)^2*(1-A0)‖≤4*‖A-A0‖+8*‖u-u0‖:=by
    have he:(1-u)^2*(1-A)-(1-u0)^2*(1-A0)=
        (1-u)^2*(A0-A)+((1-u)^2-(1-u0)^2)*(1-A0):=by ring
    have hlast:‖1-A0‖≤2:=by have hh:=norm_sub_le (1:ℂ) A0;norm_num only [norm_one] at hh;linarith
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_pow,norm_mul,norm_sub_rev A0 A]
    apply (add_le_add (mul_le_mul_of_nonneg_right (show ‖1-u‖^2≤4 by nlinarith [norm_nonneg (1-u)]) (norm_nonneg _))
      (mul_le_mul hsq hlast (norm_nonneg _) (by positivity))).trans_eq
    ring
  have hpow:=unit_disk_power_lipschitz A A0 hA hA0 2
  have he:correctionPolynomial a b A u-correctionPolynomial a b A0 u0=
      a*(A-A0)-b*(A^2-A0^2)-((1-u)^2*(1-A)-(1-u0)^2*(1-A0)):=by
    unfold correctionPolynomial;ring
  rw [he]
  calc
    _≤‖a*(A-A0)-b*(A^2-A0^2)‖+‖(1-u)^2*(1-A)-(1-u0)^2*(1-A0)‖:=norm_sub_le _ _
    _≤(‖a*(A-A0)‖+‖b*(A^2-A0^2)‖)+(4*‖A-A0‖+8*‖u-u0‖):=
      add_le_add (norm_sub_le _ _) hprod
    _≤(‖a‖*‖A-A0‖+‖b‖*(2*‖A-A0‖))+(4*‖A-A0‖+8*‖u-u0‖):=by
      simp only [norm_mul]
      exact add_le_add_right (add_le_add_left (mul_le_mul_of_nonneg_left hpow (norm_nonneg b)) _) _
    _=_:=by ring

end SpectralConsequences
#print axioms SpectralConsequences.correctionPolynomial_lipschitz
