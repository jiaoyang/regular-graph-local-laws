import Mathlib

/-! # The Ward residual keeps the extra exterior decay

With x=N^(beta/16), epsilon≤x^-15, N eta=x^24. The variance
residual is O(polylog*x^-26), before scalar gap inversion.
-/
noncomputable section
namespace SpectralConsequences

theorem exterior_ward_scale_bound (x H ε I εp u k:ℝ)
    (hx:1≤x) (hH:1≤H) (hI:0≤I) (hεp:0≤εp) (hu:0≤u)
    (hεcap:ε≤1/x^15) (hIcap:I≤1/x^15) (hεpcap:εp≤H/x^15)
    (hucap:u≤H/x^14) (hkcap:k≤H):
    Real.sqrt ε*Real.sqrt (k*(I+εp+u)/x^24)≤2*H/x^26 := by
  have hxp:0<x:=by linarith
  have hHp:0<H:=by linarith
  have h1514:1/x^15≤1/x^14:=one_div_le_one_div_of_le (pow_pos hxp _)
    (pow_le_pow_right₀ hx (by norm_num))
  have hsqrt:Real.sqrt ε≤1/x^7:=by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    apply hεcap.trans
    have hh:=one_div_le_one_div_of_le (pow_pos hxp 14) (pow_le_pow_right₀ hx (show 14≤15 by norm_num))
    simpa only[one_div,inv_pow,←pow_mul] using hh
  have hsum:I+εp+u≤3*H/x^14:=by
    have hI':I≤H/x^14:=(hIcap.trans h1514).trans (div_le_div_of_nonneg_right hH (pow_nonneg hxp.le _))
    have hεp':εp≤H/x^14:=hεpcap.trans (by
      have hh:=mul_le_mul_of_nonneg_left h1514 hHp.le
      simpa only[div_eq_mul_inv,one_div,one_mul] using hh)
    calc
      _≤H/x^14+H/x^14+H/x^14:=add_le_add (add_le_add hI' hεp') hucap
      _=_:=by ring
  have hvar:Real.sqrt (k*(I+εp+u)/x^24)≤2*H/x^19:=by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    calc
      _≤H*(3*H/x^14)/x^24:=by gcongr
      _=3*H^2/x^38:=by field_simp;ring
      _≤4*H^2/x^38:=div_le_div_of_nonneg_right (by nlinarith [sq_nonneg H]) (pow_nonneg hxp.le _)
      _=(2*H/x^19)^2:=by field_simp;ring
  calc
    _≤(1/x^7)*(2*H/x^19):=mul_le_mul hsqrt hvar (Real.sqrt_nonneg _) (by positivity)
    _=_:=by field_simp;ring

theorem exterior_residual_scale_bound (x H ε I εp u k Q:ℝ)
    (hx:1≤x) (hH:1≤H) (hQ:0<Q) (hI:0≤I) (hεp:0≤εp) (hu:0≤u)
    (hεcap:ε≤1/x^15) (hIcap:I≤1/x^15) (hεpcap:εp≤H/x^15)
    (hucap:u≤H/x^14) (hkcap:k≤H):
    Real.sqrt ε*Real.sqrt (k*(I+εp+u)/x^24)+k*εp^2+εp/Q≤
      2*H^3*(1/x^26+1/x^30+1/(x^15*Q)) := by
  have hxp:0<x:=by linarith
  have hHp:0<H:=by linarith
  have hw:=exterior_ward_scale_bound x H ε I εp u k hx hH hI hεp hu hεcap hIcap hεpcap hucap hkcap
  have hs:k*εp^2≤H^3/x^30:=by
    calc
      _≤H*(H/x^15)^2:=by gcongr
      _=_:=by field_simp;ring
  have he:εp/Q≤H/(x^15*Q):=by
    exact (div_le_div_of_nonneg_right hεpcap hQ.le).trans_eq (by ring)
  have h13:H≤H^3:=by simpa only[pow_one] using pow_le_pow_right₀ hH (show 1≤3 by norm_num)
  have hH3:0≤H^3:=pow_nonneg hHp.le _
  calc
    _≤2*H/x^26+H^3/x^30+H/(x^15*Q):=add_le_add (add_le_add hw hs) he
    _≤2*H^3/x^26+2*H^3/x^30+2*H^3/(x^15*Q):=by gcongr <;> nlinarith only[h13,hH3]
    _=_:=by ring

end SpectralConsequences
