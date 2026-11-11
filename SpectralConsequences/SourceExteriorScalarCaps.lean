import SpectralConsequences.ExteriorSourceParameters
import SpectralConsequences.ExteriorNumericalParameters
import SpectralConsequences.SourceCorrectedResiduals
import LocalLaw.SharpSamplingCounts

/-! # Every weak-prior scalar input at the actual exterior depth

Only the actual cavity weak prior is assumed. The inverse gap, correction,
selected-depth factors, nominal error and cancellation caps are all derived.
-/
open Filter
noncomputable section
set_option maxHeartbeats 1000000
namespace SpectralConsequences
open LocalLaw

def sourceExteriorScalarConstant (d:ℕ) (B:ℝ):ℝ:=
  32+8*((d-1:ℕ):ℝ)+4*(|B|+1)+2*|trivialCancellationSpectralConstant d B|
def sourceExteriorScalarExponent (a:ℕ):ℕ:=4*a+4

def sourceExteriorScalarCap (a d N:ℕ) (B:ℝ):ℝ:=
  exteriorLogCap (sourceExteriorScalarConstant d B) (sourceExteriorScalarExponent a) N

structure SourceExteriorScalarCaps (a d N:ℕ) (β B:ℝ) (z q:ℂ) : Prop where
  cap_one : 1≤sourceExteriorScalarCap a d N B
  error_nonnegative : 0≤graphPaperError a d N (logarithmicRadius β d N) z
  reference_nonnegative : 0≤(kestenMcKayStieltjes d z).im
  gap_positive : 0<sourceCorrectedGap z B
  error_cap : graphPaperError a d N (logarithmicRadius β d N) z≤1/(exteriorPower β N)^15
  reference_cap : (kestenMcKayStieltjes d z).im≤1/(exteriorPower β N)^15
  prime_cap : inflatedPrime (Real.log (N:ℝ)) (graphPaperError a d N (logarithmicRadius β d N) z)≤
    sourceExteriorScalarCap a d N B/(exteriorPower β N)^15
  tree_factor_cap : ((d-1:ℕ):ℝ)^(2*(actualCavityDepth a d N z-1))≤sourceExteriorScalarCap a d N B
  depth_cap : ((actualCavityDepth a d N z-1:ℕ):ℝ)+4≤sourceExteriorScalarCap a d N B
  prior_cap : ‖q-semicircleRoot z‖≤sourceExteriorScalarCap a d N B/(exteriorPower β N)^14
  weak_scale_cap : scalarScale (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z)≤
    sourceExteriorScalarCap a d N B/(exteriorPower β N)^14
  correction_cap : sourceTrivialCorrectionCap a d N z≤sourceExteriorScalarCap a d N B/(exteriorPower β N)^24
  gap_inverse_cap : (sourceCorrectedGap z B)⁻¹≤sourceExteriorScalarCap a d N B*exteriorPower β N
  cancellation_cap :
    trivialCancellationSpectralConstant d B*((actualCavityDepth a d N z-1:ℕ)+1)*
      ((d-1:ℕ):ℝ)^(actualCavityDepth a d N z-1)/((N:ℝ)*Real.sqrt (spectralScale z))≤
        sourceExteriorScalarCap a d N B*exteriorPower β N/(N:ℝ)

private theorem log_term_le_cap (L K A:ℝ) (p n:ℕ) (hL:1≤L) (hK:1≤K)
    (_hA:0≤A) (hAK:A≤K) (hn:n≤p):A*L^n≤K*L^p:=by
  exact mul_le_mul hAK (pow_le_pow_right₀ hL hn) (pow_nonneg (by linarith) _) (by linarith)

private theorem inverse_sqrt_exterior (s x:ℝ) (hx:1≤x) (hs:1/(2*x)≤s):
    0<Real.sqrt s ∧ 1/Real.sqrt s≤2*x := by
  have hxp:0<x:=by linarith
  have hp:0<1/(2*x):=by positivity
  have h1:1/(2*x)≤1:=by apply (div_le_one (by positivity)).mpr;linarith only[hx]
  have hspos:0<s:=hp.trans_le hs
  have hsq:(1/(2*x))^2≤s:=by nlinarith only[hp,h1,hs]
  have hroot:1/(2*x)≤Real.sqrt s:=Real.le_sqrt hp.le hspos.le |>.mpr hsq
  refine ⟨Real.sqrt_pos.mpr hspos,?_⟩
  have hh:=one_div_le_one_div_of_le hp hroot
  simpa only[one_div,inv_inv] using hh

theorem eventually_source_exterior_scalar_caps (a d:ℕ) (β B:ℝ)
    (ha:0<a) (hd:3≤d) (hβ:0<β) (hβsmall:β≤1/128):
    ∀ᶠ N:ℕ in atTop,∀E:ℝ,2+edgeWindow β N/2≤|E|→
      let z:ℂ:=(E:ℂ)+(exteriorHeight β N:ℂ)*Complex.I
      ∀q:ℂ,‖z‖≤B→
      ‖q-semicircleRoot z‖≤scalarScale (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z)→
      SourceExteriorScalarCaps a d N β B z q := by
  have hdepth:=(lowerLogLogRadius_tendsto a d ha hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_exterior_source_parameters (a:ℝ) 0 d β 0 hd hβ hβsmall,
    eventually_actualCavityDepth_le_log a d hd,hdepth] with N num hdepthLog hdepthN
  intro E hE
  dsimp only
  intro q hB hprior
  let z:ℂ:=(E:ℂ)+(exteriorHeight β N:ℂ)*Complex.I
  let L:=Real.log (N:ℝ)
  let x:=exteriorPower β N
  let ell:=actualCavityDepth a d N z-1
  let p:=sourceExteriorScalarExponent a
  let K:=sourceExteriorScalarConstant d B
  let H:=sourceExteriorScalarCap a d N B
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  have hz:0<z.im:=by simpa [z] using num.height_positive
  have hN:1≤N:=by have hh:=num.size_positive;omega
  have hNp:0<(N:ℝ):=Nat.cast_pos.mpr num.size_positive
  have hN1:1≤(N:ℝ):=by exact_mod_cast hN
  have hL:1≤L:=num.log_one
  have hLp:0<L:=by linarith
  have hx:1≤x:=Real.one_le_rpow hN1 (by linarith)
  have hxp:0<x:=by linarith
  have hk0:0≤((d-1:ℕ):ℝ):=Nat.cast_nonneg _
  have hK:1≤K:=by dsimp only[K,sourceExteriorScalarConstant];linarith [abs_nonneg B,abs_nonneg (trivialCancellationSpectralConstant d B)]
  have hK2:2≤K:=by dsimp only[K,sourceExteriorScalarConstant];linarith [abs_nonneg B,abs_nonneg (trivialCancellationSpectralConstant d B)]
  have hK5:5≤K:=by dsimp only[K,sourceExteriorScalarConstant];linarith [abs_nonneg B,abs_nonneg (trivialCancellationSpectralConstant d B)]
  have hK8:8*((d-1:ℕ):ℝ)≤K:=by dsimp only[K,sourceExteriorScalarConstant];linarith [abs_nonneg B,abs_nonneg (trivialCancellationSpectralConstant d B)]
  have hKG:4*(B+1)≤K:=by dsimp only[K,sourceExteriorScalarConstant];linarith [le_abs_self B,abs_nonneg (trivialCancellationSpectralConstant d B)]
  have hKC:2*|trivialCancellationSpectralConstant d B|≤K:=by dsimp only[K,sourceExteriorScalarConstant];linarith [abs_nonneg B]
  have hH:1≤H:=one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hL)
  have hH2:2≤H:=hK2.trans (le_mul_of_one_le_right (by linarith:0≤K) (one_le_pow₀ hL))
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hid15:1/x^15=(N:ℝ)^(-15*β/16):=by
    dsimp only[x,exteriorPower]
    rw [one_div,←Real.rpow_mul_natCast hNp.le,←Real.rpow_neg hNp.le]
    congr 1
    norm_num
    ring
  have hεcap:ε≤1/x^15:=by
    rw [hid15]
    change graphPaperError a d N (logarithmicRadius β d N) z≤_
    rw [←realSourcePaperError_nat_eq_graph a d N _ hd z hz]
    exact num.error_cap E hE
  have hI:0≤(kestenMcKayStieltjes d z).im:=by
    rw [kestenMcKayStieltjes_eq_transform d hd z hz]
    exact (kestenMcKayTransform_im_pos d _ z hz (semicircleRoot_im_pos hz).le).le
  have hIcap:(kestenMcKayStieltjes d z).im≤1/x^15:=by rw [hid15];exact num.reference_cap E hE
  have hΔ:edgeWindow β N=1/x:=by dsimp only[edgeWindow,x,exteriorPower];rw [show -β/16=-(β/16) by ring,Real.rpow_neg hNp.le];exact (one_div _).symm
  have hs:1/(2*x)≤spectralScale z:=by
    have hh:=spectralScale_exterior_lower E (exteriorHeight β N) (edgeWindow β N) num.height_positive.le hE
    rw [hΔ] at hh
    convert hh using 1
    ring
  have hroot:=inverse_sqrt_exterior (spectralScale z) x hx hs
  have hB0:0≤B:=(norm_nonneg z).trans hB
  have hgap:0<sourceCorrectedGap z B:=div_pos hroot.1 (by positivity)
  have hgapInv:(sourceCorrectedGap z B)⁻¹≤H*x:=by
    have hh:=mul_le_mul_of_nonneg_left hroot.2 (show 0≤2*(B+1) by positivity)
    have hkH:4*(B+1)≤H:=hKG.trans (le_mul_of_one_le_right (by linarith:0≤K) (one_le_pow₀ hL))
    have hh':(sourceCorrectedGap z B)⁻¹≤(4*(B+1))*x:=by
      dsimp only[sourceCorrectedGap]
      rw [inv_div]
      convert hh using 1 <;> ring
    exact hh'.trans (mul_le_mul_of_nonneg_right hkH hxp.le)
  have hscaleCap:scalarScale (spectralScale z) ε≤H/x^14:=by
    have hsMul:=scalarScale_sqrt_mul_le (spectralScale_pos hz) hε
    have hprior':scalarScale (spectralScale z) ε≤ε/Real.sqrt (spectralScale z):=
      (le_div_iff₀ hroot.1).mpr (by nlinarith only[hsMul])
    calc
      _≤(1/x^15)*(2*x):=hprior'.trans (by
        rw [div_eq_mul_inv]
        exact mul_le_mul hεcap (by simpa only[one_div] using hroot.2) (inv_nonneg.mpr hroot.1.le) (by positivity))
      _=2/x^14:=by field_simp;ring
      _≤_:=div_le_div_of_nonneg_right hH2 (pow_nonneg hxp.le _)
  have hpriorCap:‖q-semicircleRoot z‖≤H/x^14:=hprior.trans hscaleCap
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hpow:((d-1:ℕ):ℝ)^ell≤L^(2*a):=
    (pow_le_pow_right₀ (by exact_mod_cast (show 1≤d-1 by omega)) hell).trans (doubleLogRadius_base_power_bound a d N hd hL)
  have hdepthReal:(ell:ℝ)+1≤L:=by
    have hb:2≤baselineCavityDepth a d N:=by unfold baselineCavityDepth;omega
    have hh:baselineCavityDepth a d N≤actualCavityDepth a d N z:=
      (nonresonantDepth_bounds _ _).1
    have heq:ell+1=actualCavityDepth a d N z:=by dsimp only[ell];omega
    have hh':=hdepthLog z
    rw [←heq] at hh'
    simpa only[Nat.cast_add,Nat.cast_one] using hh'
  have hdepthCap:(ell:ℝ)+4≤H:=by
    have h5:5*L≤H:=by
      simpa only[pow_one] using log_term_le_cap L K 5 p 1 hL hK (by norm_num) hK5 (by dsimp only[p,sourceExteriorScalarExponent];omega)
    nlinarith only[hdepthReal,hL,h5]
  have hprime:inflatedPrime L ε≤H/x^15:=by
    have hLpCap:L^3≤H:=by
      have hh:=log_term_le_cap L K 1 p 3 hL hK (by norm_num) hK (by dsimp only[p,sourceExteriorScalarExponent];omega)
      simpa only[one_mul] using hh
    calc
      _=L^3*ε:=rfl
      _≤H*(1/x^15):=mul_le_mul hLpCap hεcap hε (by linarith)
      _=_:=by ring
  have htree:((d-1:ℕ):ℝ)^(2*ell)≤H:=by
    calc
      _=(((d-1:ℕ):ℝ)^ell)^2:=by rw [show 2*ell=ell*2 by omega,pow_mul]
      _≤(L^(2*a))^2:=pow_le_pow_left₀ (by positivity) hpow 2
      _=L^(4*a):=by rw [←pow_mul];congr 1;omega
      _≤H:=by
        have hh:=log_term_le_cap L K 1 p (4*a) hL hK (by norm_num) hK (by dsimp only[p,sourceExteriorScalarExponent];omega)
        simpa only[one_mul] using hh
  have hM:(N:ℝ)*z.im=x^24:=by
    have hh:=exterior_height_scale β N num.size_positive
    have hx24:x^24=(N:ℝ)^(3*β/2):=by
      dsimp only[x,exteriorPower]
      rw [←Real.rpow_mul_natCast hNp.le]
      congr 1
      norm_num
      ring
    simpa [z,hx24] using hh
  have hC0:sourceTrivialCorrectionCap a d N z≤H/x^24:=by
    have hcoef:8*((d-1:ℕ):ℝ)*L^(2*a)≤H:=
      log_term_le_cap L K _ p (2*a) hL hK (by positivity) hK8 (by dsimp only[p,sourceExteriorScalarExponent];omega)
    dsimp only[sourceTrivialCorrectionCap]
    rw [hM,pow_succ]
    exact div_le_div_of_nonneg_right (by nlinarith only[mul_le_mul_of_nonneg_left hpow (show 0≤8*((d-1:ℕ):ℝ) by positivity),hcoef])
      (pow_nonneg hxp.le _)
  have hcancel:trivialCancellationSpectralConstant d B*(ell+1)*((d-1:ℕ):ℝ)^ell/
      ((N:ℝ)*Real.sqrt (spectralScale z))≤H*x/(N:ℝ):=by
    have hcabs:trivialCancellationSpectralConstant d B≤|trivialCancellationSpectralConstant d B|:=le_abs_self _
    have hcL:2*|trivialCancellationSpectralConstant d B| *L^(2*a+1)≤H:=
      log_term_le_cap L K _ p (2*a+1) hL hK (by positivity) hKC (by dsimp only[p,sourceExteriorScalarExponent];omega)
    have hcap:trivialCancellationSpectralConstant d B*(ell+1)*((d-1:ℕ):ℝ)^ell/
        ((N:ℝ)*Real.sqrt (spectralScale z))≤
        |trivialCancellationSpectralConstant d B| *L*L^(2*a)*(2*x)/(N:ℝ):=by
      rw [div_eq_mul_inv,mul_inv_rev]
      have hh:=mul_le_mul hdepthReal hpow (by positivity) hLp.le
      have hh':=mul_le_mul hcabs hh (by positivity) (abs_nonneg _)
      have hh'':=mul_le_mul hh' (by simpa only[one_div] using hroot.2) (inv_nonneg.mpr hroot.1.le) (by positivity)
      convert mul_le_mul_of_nonneg_right hh'' (inv_nonneg.mpr hNp.le) using 1 <;> ring
    apply hcap.trans
    have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcL hxp.le) (inv_nonneg.mpr hNp.le)
    convert hh using 1
    rw [pow_succ]
    ring
  exact ⟨hH,hε,hI,hgap,hεcap,hIcap,hprime,htree,hdepthCap,hpriorCap,hscaleCap,hC0,hgapInv,hcancel⟩

end SpectralConsequences
