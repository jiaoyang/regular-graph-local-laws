import SpectralConsequences.ExteriorNumericalParameters

/-! # The two corrected-scalar stability absorptions at the exterior scales -/
noncomputable section
namespace SpectralConsequences

theorem exterior_stability_smallness (x H ell u C0 G:ℝ)
    (hx:1≤x) (hH:1≤H) (hell:ell≤H) (hu:0≤u) (hC0:0≤C0) (hG:0≤G)
    (hucap:u≤H/x^14) (hCcap:C0≤H/x^24) (hGcap:G≤H*x)
    (hsmall:6*H^4≤x^13):
    ell*u≤1/2 ∧ ell*(u+C0*(G+1))*G≤1/2 := by
  have hxp:0<x:=by linarith
  have hHp:0<H:=by linarith
  have hH2:H^2≤H^4:=pow_le_pow_right₀ hH (by norm_num)
  have hxpow:x^13≤x^14:=pow_le_pow_right₀ hx (by norm_num)
  have hfirst:2*H^2≤x^14:=by nlinarith only[hH2,hsmall,hxpow,pow_nonneg hHp.le 4]
  constructor
  · calc
      _≤H*(H/x^14):=by gcongr
      _=H^2/x^14:=by ring
      _≤1/2:=by apply (div_le_iff₀ (pow_pos hxp _)).mpr;linarith only[hfirst]
  · have hHX:1≤H*x:=one_le_mul_of_one_le_of_one_le hH hx
    have hstep:u+C0*(G+1)≤H/x^14+2*H^2/x^23:=by
      calc
        _≤H/x^14+(H/x^24)*(H*x+1):=by gcongr
        _≤H/x^14+(H/x^24)*(2*H*x):=by gcongr;linarith only[hHX]
        _=_:=by field_simp;ring
    have h23:1/x^22≤1/x^13:=one_div_le_one_div_of_le (pow_pos hxp _)
      (pow_le_pow_right₀ hx (by norm_num))
    have hH3:H^3≤H^4:=pow_le_pow_right₀ hH (by norm_num)
    calc
      _≤H*(H/x^14+2*H^2/x^23)*(H*x):=by gcongr
      _=H^3/x^13+2*H^4/x^22:=by field_simp;ring
      _≤H^4/x^13+2*H^4/x^13:=by
        exact add_le_add (div_le_div_of_nonneg_right hH3 (pow_nonneg hxp.le _))
          (by
            calc
              _=(2*H^4)*(1/x^22):=by ring
              _≤(2*H^4)*(1/x^13):=mul_le_mul_of_nonneg_left h23 (by positivity)
              _=_:=by ring)
      _=3*H^4/x^13:=by ring
      _≤1/2:=by apply (div_le_iff₀ (pow_pos hxp _)).mpr;linarith only[hsmall]

end SpectralConsequences
