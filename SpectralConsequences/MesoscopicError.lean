import LocalLaw.SourceLocalLawIdentifiers
import LocalLaw.ParameterGrowth
import LocalLaw.ReferenceBounds

/-! # A polynomial source-error bound at a mesoscopic height -/
open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw

 def countingHeight (β:ℝ) (N:ℕ):ℝ := (N:ℝ)^(-β)

theorem mesoscopic_baseErrorTerms_bound (d N:ℕ) (β I:ℝ)
    (hd:3≤d) (hN:1≤N) (hβ:0≤β) (hβsmall:β≤1/3) (hI:I≤2) :
    baseErrorTerms d N (logarithmicRadius β d N) (countingHeight β N) I≤
      (((d-1:ℕ):ℝ)+3)*(N:ℝ)^(-β) := by
  let f:ℝ:=(N:ℝ)^β
  let X:ℝ:=(N:ℝ)*countingHeight β N
  have hNp:0<(N:ℝ):=by exact_mod_cast (show 0<N by omega)
  have hN1:1≤(N:ℝ):=by exact_mod_cast hN
  have hfp:0<f:=Real.rpow_pos_of_pos hNp β
  have hf1:1≤f:=Real.one_le_rpow hN1 hβ
  have hXid:X=(N:ℝ)^(1-β):=by
    dsimp only[X,countingHeight]
    calc
      _=(N:ℝ)^(1:ℝ)*(N:ℝ)^(-β):=by rw [Real.rpow_one]
      _=(N:ℝ)^(1-β):=by rw [←Real.rpow_add hNp];rfl
  have hX:f^2≤X:=by
    rw [hXid,←Real.rpow_mul_natCast hNp.le β 2]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    norm_num
    linarith only[hβsmall]
  have hXp:0<X:=lt_of_lt_of_le (sq_pos_of_pos hfp) hX
  have hX1:1≤X:=(by nlinarith only[hf1]:1≤f^2).trans hX
  have hv:Real.sqrt (I/X)≤2/f:=by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    calc
      I/X≤2/X:=div_le_div_of_nonneg_right hI hXp.le
      _≤2/f^2:=div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hfp) hX
      _≤(2/f)^2:=by
        rw [div_pow]
        norm_num
        exact div_le_div_of_nonneg_right (by norm_num : (2:ℝ)≤4) (sq_nonneg f)
  have hfrac:(X^(2/3:ℝ))⁻¹≤1/f:=by
    have hs:f≤Real.sqrt X:=by
      have hh:=Real.sqrt_le_sqrt hX
      simpa only[Real.sqrt_sq_eq_abs,abs_of_pos hfp] using hh
    have hh:=Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num:(1/2:ℝ)≤2/3)
    have hden:f≤X^(2/3:ℝ):=hs.trans (by simpa only[Real.sqrt_eq_rpow] using hh)
    simpa only[one_div] using one_div_le_one_div_of_le hfp hden
  have hloc:=logarithmicRadius_inverse_bound β d N hd hN
  have hinv:1/f=(N:ℝ)^(-β):=by rw [Real.rpow_neg hNp.le];exact one_div f
  change (((d-1:ℕ):ℝ)^logarithmicRadius β d N)⁻¹+Real.sqrt (I/X)+(X^(2/3:ℝ))⁻¹≤_
  have hloc':(((d-1:ℕ):ℝ)^logarithmicRadius β d N)⁻¹≤((d-1:ℕ):ℝ)/f:=hloc
  calc
    _≤((d-1:ℕ):ℝ)/f+2/f+1/f:=add_le_add (add_le_add hloc' hv) hfrac
    _=(((d-1:ℕ):ℝ)+3)*(1/f):=by ring
    _= _:=by rw [hinv]

theorem realSourcePaperError_mesoscopic_bound (a:ℝ) (d N:ℕ) (β:ℝ)
    (hd:3≤d) (hN:1≤N) (hβ:0≤β) (hβsmall:β≤1/3)
    (hL:1≤Real.log (N:ℝ)) (z:ℂ) (hz:0<z.im) (hheight:z.im=countingHeight β N) :
    realSourcePaperError a d N (logarithmicRadius β d N) z≤
      (((d-1:ℕ):ℝ)+3)*Real.log (N:ℝ)^(8*a+4)*(N:ℝ)^(-β) := by
  let L:=Real.log (N:ℝ)
  have hLp:0<L:=by dsimp only[L];linarith
  have hI:(kestenMcKayStieltjes d z).im≤2:=by
    rw [kestenMcKayStieltjes_eq_transform d hd z hz]
    exact ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (kestenMcKayTransform_norm_le_two d hd z hz)
  have ht:=mesoscopic_baseErrorTerms_bound d N β _ hd hN hβ hβsmall hI
  rw [←hheight] at ht
  have hb:0≤L^(8*a)*baseErrorTerms d N (logarithmicRadius β d N) z.im (kestenMcKayStieltjes d z).im:=
    mul_nonneg (Real.rpow_nonneg hLp.le _) (baseErrorTerms_nonnegative _ _ _ _ _ hz.le)
  have hh:realSourcePaperError a d N (logarithmicRadius β d N) z≤
      L^4*(L^(8*a)*baseErrorTerms d N (logarithmicRadius β d N) z.im (kestenMcKayStieltjes d z).im):=
    (inflateError_bounds hL hb).2
  apply hh.trans
  calc
    _≤L^4*(L^(8*a)*((((d-1:ℕ):ℝ)+3)*(N:ℝ)^(-β))):=by gcongr
    _= _:=by
      rw [show 8*a+4=4+8*a by ring,Real.rpow_add hLp]
      rw [show L^(4:ℝ)=L^4 from Real.rpow_natCast L 4]
      ring

end SpectralConsequences
