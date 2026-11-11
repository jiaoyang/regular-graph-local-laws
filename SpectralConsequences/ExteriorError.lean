import SpectralConsequences.MesoscopicError
import SpectralConsequences.KestenMcKayExterior

/-! # The actual source error at the exterior rigidity height

The reference imaginary part is bounded by its normalized density integral.
All three terms in the nominal error retain the original localization radius.
-/
open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw

def exteriorHeight (β:ℝ) (N:ℕ):ℝ := (N:ℝ)^(-1+3*β/2)
def edgeWindow (β:ℝ) (N:ℕ):ℝ := (N:ℝ)^(-β/16)

theorem exterior_height_scale (β:ℝ) (N:ℕ) (hN:0<N):
    (N:ℝ)*exteriorHeight β N=(N:ℝ)^(3*β/2):=by
  have hp:0<(N:ℝ):=Nat.cast_pos.mpr hN
  calc
    _=(N:ℝ)^(1:ℝ)*(N:ℝ)^(-1+3*β/2):=by rw [Real.rpow_one];rfl
    _=_:=by rw [←Real.rpow_add hp];congr 1;ring

theorem spectralScale_exterior_lower (E η Δ:ℝ) (hη:0≤η) (hE:2+Δ/2≤|E|):
    Δ/2≤spectralScale ((E:ℂ)+(η:ℂ)*Complex.I):=by
  have ha:|E|-2≤|E-2|:=by
    simpa using (le_abs_self (|E|-|2|)).trans (abs_abs_sub_abs_le_abs_sub E 2)
  have hb:|E|-2≤|E+2|:=by
    simpa using (le_abs_self (|E|-|(-2:ℝ)|)).trans (abs_abs_sub_abs_le_abs_sub E (-2))
  have hm:Δ/2 ≤ min |E-2| |E+2|:=le_min (by linarith) (by linarith)
  simpa only[spectralScale,edgeDistance,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,sub_zero,add_zero,
    Complex.add_im,Complex.mul_im,zero_add] using (le_add_of_le_of_nonneg hm hη)

theorem exterior_baseErrorTerms_bound (d N:ℕ) (β I:ℝ)
    (hd:3≤d) (hN:1≤N) (hβsmall:β≤1/128)
    (hI:I≤4*exteriorHeight β N/(edgeWindow β N)^2):
    baseErrorTerms d N (logarithmicRadius β d N) (exteriorHeight β N) I≤
      (((d-1:ℕ):ℝ)+3)*(N:ℝ)^(-β):=by
  let f:ℝ:=(N:ℝ)^β
  let Δ:=edgeWindow β N
  let η:=exteriorHeight β N
  let X:ℝ:=(N:ℝ)*η
  have hNp:0<(N:ℝ):=by exact_mod_cast (show 0<N by omega)
  have hN1:1≤(N:ℝ):=by exact_mod_cast hN
  have hfp:0<f:=Real.rpow_pos_of_pos hNp β
  have hΔ:0<Δ:=Real.rpow_pos_of_pos hNp _
  have hη:0<η:=Real.rpow_pos_of_pos hNp _
  have hXp:0<X:=mul_pos hNp hη
  have hden:f^2≤(N:ℝ)*Δ^2:=by
    have hid:(N:ℝ)*Δ^2=(N:ℝ)^(1-β/8):=by
      dsimp only[Δ,edgeWindow]
      rw [←Real.rpow_mul_natCast hNp.le (-β/16) 2]
      calc
        _=(N:ℝ)^(1:ℝ)*(N:ℝ)^((-β/16)*(2:ℕ)):=by rw [Real.rpow_one]
        _=_:=by rw [←Real.rpow_add hNp];congr 1;push_cast;ring
    rw [hid,←Real.rpow_mul_natCast hNp.le β 2]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast;linarith only[hβsmall])
  have hvariance:Real.sqrt (I/X)≤2/f:=by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hquot:(4*η/Δ^2)/X=4/((N:ℝ)*Δ^2):=by dsimp only[X];field_simp;ring
    calc
      I/X≤(4*η/Δ^2)/X:=div_le_div_of_nonneg_right hI hXp.le
      _=4/((N:ℝ)*Δ^2):=hquot
      _≤4/f^2:=div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hfp) hden
      _=(2/f)^2:=by rw [div_pow];norm_num
  have hfrac:(X^(2/3:ℝ))⁻¹=(N:ℝ)^(-β):=by
    have hid:X=(N:ℝ)^(3*β/2):=exterior_height_scale β N (by omega)
    rw [hid,←Real.rpow_mul hNp.le,←Real.rpow_neg hNp.le]
    congr 1
    ring
  have hinv:1/f=(N:ℝ)^(-β):=by rw [Real.rpow_neg hNp.le];exact one_div f
  have hloc:=logarithmicRadius_inverse_bound β d N hd hN
  change (((d-1:ℕ):ℝ)^logarithmicRadius β d N)⁻¹+Real.sqrt (I/X)+(X^(2/3:ℝ))⁻¹≤_
  rw [hfrac,←hinv]
  calc
    _≤((d-1:ℕ):ℝ)/f+2/f+1/f:=add_le_add_right (add_le_add hloc hvariance) _
    _=(((d-1:ℕ):ℝ)+3)*(1/f):=by ring
    _=_:=by rw [hinv]

theorem realSourcePaperError_exterior_bound (a:ℝ) (d N:ℕ) (β E:ℝ)
    (hd:3≤d) (hN:1≤N) (hβsmall:β≤1/128)
    (hL:1≤Real.log (N:ℝ)) (hE:2+edgeWindow β N/2≤|E|):
    realSourcePaperError a d N (logarithmicRadius β d N)
      ((E:ℂ)+(exteriorHeight β N:ℂ)*Complex.I)≤
      (((d-1:ℕ):ℝ)+3)*Real.log (N:ℝ)^(8*a+4)*(N:ℝ)^(-β):=by
  let z:ℂ:=(E:ℂ)+(exteriorHeight β N:ℂ)*Complex.I
  let L:=Real.log (N:ℝ)
  have hNp:0<(N:ℝ):=by exact_mod_cast (show 0<N by omega)
  have hη:0<exteriorHeight β N:=Real.rpow_pos_of_pos hNp _
  have hΔ:0<edgeWindow β N:=Real.rpow_pos_of_pos hNp _
  have hz:0<z.im:=by simpa only[z,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
    Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] using hη
  have hI:(kestenMcKayStieltjes d z).im≤4*exteriorHeight β N/(edgeWindow β N)^2:=by
    have hh:=kestenMcKayStieltjes_im_exterior d hd E (exteriorHeight β N) (edgeWindow β N/2)
      hη (by positivity) hE
    apply hh.trans_eq
    field_simp
    ring
  have ht:=exterior_baseErrorTerms_bound d N β _ hd hN hβsmall hI
  have hheight:z.im=exteriorHeight β N:=by simp [z]
  rw [←hheight] at ht
  have hb:0≤L^(8*a)*baseErrorTerms d N (logarithmicRadius β d N) z.im (kestenMcKayStieltjes d z).im:=
    mul_nonneg (Real.rpow_nonneg (by dsimp only[L];linarith) _) (baseErrorTerms_nonnegative _ _ _ _ _ hz.le)
  have hh:realSourcePaperError a d N (logarithmicRadius β d N) z≤
      L^4*(L^(8*a)*baseErrorTerms d N (logarithmicRadius β d N) z.im (kestenMcKayStieltjes d z).im):=
    (inflateError_bounds hL hb).2
  apply hh.trans
  calc
    _≤L^4*(L^(8*a)*((((d-1:ℕ):ℝ)+3)*(N:ℝ)^(-β))):=by gcongr
    _=_:=by
      rw [show 8*a+4=4+8*a by ring,Real.rpow_add (by dsimp only[L];linarith : 0<L)]
      rw [show L^(4:ℝ)=L^4 from Real.rpow_natCast L 4]
      ring

end SpectralConsequences
