import Mathlib

/-! # A finite numerical engine for the corrected exterior trace

The residuals retain the Ward variance scale. No residual or corrected trace
estimate is claimed probabilistically here: actual Section 7 estimates feed
these explicit finite inequalities.
-/
noncomputable section
namespace SpectralConsequences

private theorem inverse_power_le_inverse (x:ℝ) (hx:1≤x) (n:ℕ) (hn:1≤n):
    1/x^n≤1/x:=by
  have hp:0<x:=by linarith
  exact one_div_le_one_div_of_le hp (by simpa only[pow_one] using pow_le_pow_right₀ hx hn)

theorem exterior_correction_budget_bound
    (x N Q H V ell u Rc Rt C0 G cancel:ℝ)
    (hx:1≤x) (hH:1≤H) (hV:1≤V) (hN:x^26≤N) (hQ:x^11≤Q)
    (hellH:ell≤H) (hu:0≤u)
    (hC0:0≤C0) (hG:0≤G)
    (huCap:u≤H/x^14) (hC0Cap:C0≤H/x^24) (hGCap:G≤H*x)
    (hRcCap:Rc≤H*V*(1/x^26+1/x^30+1/(x^15*Q)))
    (hRtCap:Rt≤H*V*(1/x^26+1/x^30+1/(x^15*Q)))
    (hcancel:cancel≤H*x/N) :
    x^24*(Rt+16*ell*u^2+24*Rc*G+48*ell*C0^2*G^3+cancel)≤140*H^6*V/x:=by
  have hxp:0<x:=by linarith
  have hHp:0<H:=by linarith
  have hVp:0<V:=by linarith
  have hNp:0<N:=lt_of_lt_of_le (pow_pos hxp _) hN
  have hQp:0<Q:=lt_of_lt_of_le (pow_pos hxp _) hQ
  let F:=1/x^26+1/x^30+1/(x^15*Q)
  have hF:0≤F:=by dsimp only[F];positivity
  have hmain:Rt+24*Rc*G≤25*H^2*V*x*F:=by
    have hHX:1≤H*x:=one_le_mul_of_one_le_of_one_le hH hx
    calc
      _≤H*V*F+24*(H*V*F)*(H*x):=by gcongr
      _=(H*V*F)*(1+24*H*x):=by ring
      _≤(H*V*F)*(25*H*x):=by gcongr;nlinarith only[hHX]
      _=_:=by ring
  have hQdec:x^10/Q≤1/x:=by
    calc
      _≤x^10/x^11:=div_le_div_of_nonneg_left (pow_nonneg hxp.le _) (pow_pos hxp _) hQ
      _=_:=by rw [pow_succ];field_simp;ring
  have hFdec:1/x+1/x^5+x^10/Q≤3/x:=by
    have h5:=inverse_power_le_inverse x hx 5 (by norm_num)
    calc
      _≤1/x+1/x+1/x:=by linarith only[h5,hQdec]
      _=_:=by ring
  have hm:x^24*(Rt+24*Rc*G)≤75*H^2*V/x:=by
    calc
      _≤x^24*(25*H^2*V*x*F):=mul_le_mul_of_nonneg_left hmain (pow_nonneg hxp.le _)
      _=25*H^2*V*(1/x+1/x^5+x^10/Q):=by dsimp only[F];field_simp;ring
      _≤25*H^2*V*(3/x):=by gcongr
      _=_:=by ring
  have hp:x^24*(16*ell*u^2)≤16*H^3/x:=by
    calc
      _≤x^24*(16*H*(H/x^14)^2):=by gcongr
      _=16*H^3*(1/x^4):=by field_simp;ring
      _≤16*H^3*(1/x):=mul_le_mul_of_nonneg_left (inverse_power_le_inverse x hx 4 (by norm_num)) (by positivity)
      _=_:=by ring
  have hc:x^24*(48*ell*C0^2*G^3)≤48*H^6/x:=by
    calc
      _≤x^24*(48*H*(H/x^24)^2*(H*x)^3):=by gcongr
      _=48*H^6*(1/x^21):=by field_simp;ring
      _≤48*H^6*(1/x):=mul_le_mul_of_nonneg_left (inverse_power_le_inverse x hx 21 (by norm_num)) (by positivity)
      _=_:=by ring
  have hcan:x^24*cancel≤H/x:=by
    calc
      _≤x^24*(H*x/N):=mul_le_mul_of_nonneg_left hcancel (pow_nonneg hxp.le _)
      _≤x^24*(H*x/x^26):=by gcongr
      _=_:=by field_simp;ring
  have h2:H^2≤H^6:=pow_le_pow_right₀ hH (by norm_num)
  have h3:H^3≤H^6:=pow_le_pow_right₀ hH (by norm_num)
  have h1:H≤H^6:=by simpa only[pow_one] using pow_le_pow_right₀ hH (show 1≤6 by norm_num)
  have h3V:H^3≤H^6*V:=h3.trans (le_mul_of_one_le_right (pow_nonneg hHp.le _) hV)
  have h6V:H^6≤H^6*V:=le_mul_of_one_le_right (pow_nonneg hHp.le _) hV
  have h1V:H≤H^6*V:=h1.trans h6V
  have h2V:H^2*V≤H^6*V:=mul_le_mul_of_nonneg_right h2 hVp.le
  have hcoef:75*H^2*V+16*H^3+48*H^6+H≤140*H^6*V:=by nlinarith only[h2V,h3V,h6V,h1V]
  calc
    _=x^24*(Rt+24*Rc*G)+x^24*(16*ell*u^2)+x^24*(48*ell*C0^2*G^3)+x^24*cancel:=by ring
    _≤75*H^2*V/x+16*H^3/x+48*H^6/x+H/x:=add_le_add (add_le_add (add_le_add hm hp) hc) hcan
    _=(75*H^2*V+16*H^3+48*H^6+H)/x:=by ring
    _≤_:=div_le_div_of_nonneg_right hcoef hxp.le

end SpectralConsequences
