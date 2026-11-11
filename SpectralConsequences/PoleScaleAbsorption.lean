import SpectralConsequences.TrivialCorrections
import SpectralConsequences.SourceSpectralBox
import LocalLaw.SwitchingQParameters

/-! Genuine near-pole/away-pole absorption. The fractional source-error
floor alone absorbs Psi times the regular eigenvalue pole into epsilon². -/
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem fractional_floor_three_halves (x ε:ℝ)(hx:0<x)(_hε:0≤ε)
    (hfloor:1/x^(2/3:ℝ)≤ε):1/x≤ε*Real.sqrt ε:=by
  have hεp:0<ε:=lt_of_lt_of_le (by positivity) hfloor
  have hh:=Real.rpow_le_rpow (by positivity:0≤1/x^(2/3:ℝ)) hfloor (by norm_num:(0:ℝ)≤3/2)
  have he:(1/x^(2/3:ℝ))^(3/2:ℝ)=1/x:=by
    rw [one_div,Real.inv_rpow (Real.rpow_nonneg hx.le _),←Real.rpow_mul hx.le]
    norm_num
  have he':ε^(3/2:ℝ)=ε*Real.sqrt ε:=by
    rw [Real.sqrt_eq_rpow,show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hεp,Real.rpow_one]
  rwa [he,he'] at hh

theorem fractional_floor_inverse (x ε:ℝ)(hx:1≤x)(hfloor:1/x^(2/3:ℝ)≤ε):1/x≤ε:=by
  apply le_trans _ hfloor
  exact one_div_le_one_div_of_le (by positivity) (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx (by norm_num:(2/3:ℝ)≤1))

def poleScaleConstant (τ B:ℝ):ℝ:=(Real.sqrt ((τ-2)/2))⁻¹+B/((τ-2)/2)

theorem pole_scale_quadratic (N τ B ε:ℝ)(z:ℂ)(hN:0<N)(hτ:2<τ)(hB:0≤B)
    (hz:0<z.im)(hzB:z.im≤B)(hε:0≤ε)(hsample:1≤N*z.im)
    (hfloor:1/(N*z.im)^(2/3:ℝ)≤ε):
    scalarScale (spectralScale z) ε*‖(N:ℂ)⁻¹*((τ:ℂ)-z)⁻¹‖≤poleScaleConstant τ B*ε^2:=by
  let g:ℝ:=(τ-2)/2
  have hg:0<g:=by dsimp only [g];linarith
  have hroot:0<Real.sqrt g:=Real.sqrt_pos.mpr hg
  have hgapIm:z.im≤‖(τ:ℂ)-z‖:=by
    have hh:=Complex.abs_im_le_norm ((τ:ℂ)-z)
    simpa only [Complex.sub_im,Complex.ofReal_im,zero_sub,abs_neg,abs_of_pos hz] using hh
  have hp:‖(N:ℂ)⁻¹*((τ:ℂ)-z)⁻¹‖=1/N/‖(τ:ℂ)-z‖:=by
    rw [norm_mul,norm_inv,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN]
    ring
  have hpsample:‖(N:ℂ)⁻¹*((τ:ℂ)-z)⁻¹‖≤1/(N*z.im):=by
    rw [hp]
    exact (div_le_div_of_nonneg_left (by positivity) hz hgapIm).trans_eq (by field_simp)
  have hεfloor:1/(N*z.im)≤ε:=fractional_floor_inverse _ _ hsample hfloor
  have hscale:0≤scalarScale (spectralScale z) ε:=scalarScale_nonneg hε
  have haway:0≤B/g:=div_nonneg hB hg.le
  have hnear:0≤(Real.sqrt g)⁻¹:=inv_nonneg.mpr hroot.le
  by_cases hclose:‖(τ:ℂ)-z‖<g
  · have hreal:τ-z.re<g:=by
      have hh:=Complex.abs_re_le_norm ((τ:ℂ)-z)
      simp only [Complex.sub_re,Complex.ofReal_re] at hh
      exact lt_of_le_of_lt ((le_abs_self _).trans hh) hclose
    have he:g≤edgeDistance z:=by
      have hzre:2+g<z.re:=by dsimp only [g] at *;linarith
      unfold edgeDistance
      rw [abs_of_pos (by linarith:z.re-2>0),abs_of_pos (by linarith:z.re+2>0)]
      apply le_min <;>linarith
    have hs:g≤spectralScale z+ε:=by unfold spectralScale;linarith
    have hscale':scalarScale (spectralScale z) ε≤ε/Real.sqrt g:=
      div_le_div_of_nonneg_left hε hroot (Real.sqrt_le_sqrt hs)
    calc
      _≤(ε/Real.sqrt g)*ε:=mul_le_mul hscale' (hpsample.trans hεfloor) (norm_nonneg _) (by positivity)
      _=(Real.sqrt g)⁻¹*ε^2:=by ring
      _≤poleScaleConstant τ B*ε^2:=by
        dsimp only [poleScaleConstant]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right haway) (sq_nonneg ε)
  · have hfar:g≤‖(τ:ℂ)-z‖:=le_of_not_gt hclose
    have hpfar:‖(N:ℂ)⁻¹*((τ:ℂ)-z)⁻¹‖≤(1/N)/g:=by
      rw [hp]
      exact div_le_div_of_nonneg_left (by positivity) hg hfar
    have hthree:1/N≤B*(ε*Real.sqrt ε):=by
      have hh:=fractional_floor_three_halves (N*z.im) ε (mul_pos hN hz) hε hfloor
      have hm:=mul_le_mul_of_nonneg_left hh hz.le
      have he:z.im*(1/(N*z.im))=1/N:=by field_simp;ring
      rw [he] at hm
      exact hm.trans (by nlinarith [mul_le_mul_of_nonneg_right hzB (mul_nonneg hε (Real.sqrt_nonneg ε))])
    have hsqrt:Real.sqrt ε*(1/N)≤B*ε^2:=by
      have hh:=mul_le_mul_of_nonneg_left hthree (Real.sqrt_nonneg ε)
      have he:Real.sqrt ε*(B*(ε*Real.sqrt ε))=B*ε^2:=by
        calc
          _=B*ε*(Real.sqrt ε)^2:=by ring
          _=_:=by rw [Real.sq_sqrt hε];ring
      exact hh.trans_eq he
    calc
      _≤Real.sqrt ε*((1/N)/g):=mul_le_mul (scalarScale_le_sqrt (spectralScale_pos hz) hε)
        hpfar (norm_nonneg _) (Real.sqrt_nonneg ε)
      _=(Real.sqrt ε*(1/N))/g:=by ring
      _≤(B*ε^2)/g:=div_le_div_of_nonneg_right hsqrt hg.le
      _=(B/g)*ε^2:=by ring
      _≤poleScaleConstant τ B*ε^2:=by
        dsimp only [poleScaleConstant]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hnear) (sq_nonneg ε)

theorem regularSpectralRadius_gt_two (d:ℕ)(hd:3≤d):2<regularSpectralRadius d:=by
  have hd':(3:ℝ)≤d:=by exact_mod_cast hd
  have hs:0<Real.sqrt ((d:ℝ)-1):=Real.sqrt_pos.mpr (by linarith)
  have hs2:=Real.sq_sqrt (show 0≤(d:ℝ)-1 by linarith)
  have hp:0<((d:ℝ)-2)^2:=sq_pos_of_pos (by linarith)
  unfold regularSpectralRadius
  apply (lt_div_iff₀ hs).mpr
  nlinarith [Real.sqrt_nonneg ((d:ℝ)-1)]

theorem eventually_source_pole_scale_quadratic (a b d:ℕ)(B:ℝ)(hd:3≤d)(hB:0≤B):
    ∀ᶠ N:ℕ in Filter.atTop,∀(z:ℂ),0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀r:ℕ,
      scalarScale (spectralScale z) (graphPaperError a d N r z)*‖trivialPole N d z‖≤
        poleScaleConstant (regularSpectralRadius d) B*(graphPaperError a d N r z)^2:=by
  filter_upwards [eventually_log_ge_nat 1,Filter.eventually_ge_atTop 1] with N hlog hN
  intro z hz hfloor hzB r
  have hn:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  have hs:1≤(N:ℝ)*z.im:=by
    have hh:=(div_le_iff₀ hn).mp hfloor
    exact (one_le_pow₀ hlog).trans (by linarith)
  have hfrac:1/((N:ℝ)*z.im)^(2/3:ℝ)≤graphPaperError a d N r z:=
    (div_le_div_of_nonneg_right (one_le_pow₀ hlog) (Real.rpow_nonneg (by positivity) _)).trans
      (graphPaperError_fractional_lower a d N r z hlog hz.le)
  have hη:z.im≤B:=((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans hzB
  have h:=pole_scale_quadratic (N:ℝ) (regularSpectralRadius d) B (graphPaperError a d N r z) z hn
    (regularSpectralRadius_gt_two d hd) hB hz hη
    (graphPaperError_nonnegative _ _ _ _ _ hN hz.le) hs hfrac
  convert h using 1
  dsimp only [trivialPole,regularSpectralRadius,treeEdgeWeight]
  push_cast
  ring

end SpectralConsequences
#print axioms SpectralConsequences.eventually_source_pole_scale_quadratic
