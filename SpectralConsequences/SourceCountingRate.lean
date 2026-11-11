import SpectralConsequences.MesoscopicError
import SpectralConsequences.SourceSpectralBox
import SpectralConsequences.CDFComparison
import LocalLaw.SourceTheorem42

/-! # A positive polynomial counting rate from the actual uniform local law

This uses only the trace part of Theorem 4.2 and Poisson smoothing. It proves
a CDF estimate, not edge confinement or unclamped eigenvalue rigidity.
-/
open Filter Set
noncomputable section
set_option maxHeartbeats 1000000
namespace SpectralConsequences
open LocalLaw
local instance sourceCountingRateDecidable (p:Prop):Decidable p:=Classical.propDecidable p

 def SourceCountingCDFGood {N d:ℕ} (β:ℝ) (g:RegularGraph N d):Prop:=
  ∀E,|empiricalCDF (sortedEigenvalues g.H_hermitian) E-kestenMcKayCDF d E|≤(N:ℝ)^(-β/8)

theorem eventually_source_local_law_implies_counting_rate (d:ℕ) (a b β C:ℝ)
    (hd:3≤d) (hβ:0<β) (hβsmall:β≤1/3):
    ∀ᶠ N:ℕ in atTop,∀g:RegularGraph N d,
      (∀z:ℂ,0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
        RealSourceLocalLawAt (by omega) a (logarithmicRadius β d N) C z g)→
      SourceCountingCDFGood β g := by
  let M:=max 2 (regularSpectralRadius d)
  let K:=(((d-1:ℕ):ℝ)+3)
  let T:=2*(M+2)/Real.pi
  let R:=2*kestenMcKayDensityCap d+4/Real.pi
  have hT:0≤T:=by dsimp only[T,M];positivity
  have hR:0≤R:=by have hh:=(kestenMcKayDensityCap_positive d hd).le;dsimp only[R];positivity
  filter_upwards [eventually_const_mul_log_rpow_le K (8*a+4) (β/4) (by linarith),
    eventually_const_mul_log_rpow_le C 0 (β/8) (by linarith),
    eventually_const_mul_log_rpow_le (T+R) 0 (β/8) (by linarith),
    eventually_const_mul_log_rpow_le 1 b (1-β) (by linarith),
    eventually_log_ge_nat 1,eventually_ge_atTop 1]
    with N herror hconst hCDFconst hfloor hL hN
  intro g hsource
  have hNp:0<(N:ℝ):=by exact_mod_cast (show 0<N by omega)
  have hN1:1≤(N:ℝ):=by exact_mod_cast hN
  have hη:0<countingHeight β N:=Real.rpow_pos_of_pos hNp _
  have hη1:countingHeight β N≤1:=by
    exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hfloor':Real.log (N:ℝ)^b/(N:ℝ)≤countingHeight β N:=by
    simp only[Real.rpow_zero,one_mul] at hfloor
    apply (div_le_iff₀ hNp).mpr
    have hid:(N:ℝ)^(1-β)=countingHeight β N*(N:ℝ):=by
      dsimp only[countingHeight]
      calc
        _=(N:ℝ)^(-β+1):=by congr 1;ring
        _=(N:ℝ)^(-β)*(N:ℝ)^1:=Real.rpow_add hNp _ _
        _=_:=by rw [Real.rpow_one]
    exact hfloor.trans_eq hid
  have herror' : ∀z:ℂ,0<z.im→z.im=countingHeight β N→
      realSourcePaperError a d N (logarithmicRadius β d N) z≤(N:ℝ)^(-3*β/4):=by
    intro z hz hheight
    apply (realSourcePaperError_mesoscopic_bound a d N β hd hN hβ.le hβsmall hL z hz hheight).trans
    have hh:=mul_le_mul_of_nonneg_right herror (Real.rpow_nonneg hNp.le (-β))
    calc
      _≤(N:ℝ)^(β/4)*(N:ℝ)^(-β):=hh
      _=(N:ℝ)^(-3*β/4):=by rw [←Real.rpow_add hNp];congr 1;ring
  have hconst':C≤(N:ℝ)^(β/8):=by simpa only[Real.rpow_zero,mul_one] using hconst
  have htrace:∀u∈Icc (-M-2) (M+2),
      ‖finiteStieltjes (sortedEigenvalues g.H_hermitian) ((u:ℂ)+(countingHeight β N:ℂ)*Complex.I)-
        kestenMcKayStieltjes d ((u:ℂ)+(countingHeight β N:ℂ)*Complex.I)‖≤(N:ℝ)^(-β/4):=by
    intro u _
    let z:ℂ:=(u:ℂ)+(countingHeight β N:ℂ)*Complex.I
    have hheight:z.im=countingHeight β N:=by simp [z]
    have hz:0<z.im:=hheight ▸ hη
    have hlocal:‖empiricalTransform g.H z-kestenMcKayStieltjes d z‖≤
        C*scalarScale (spectralScale z) (realSourcePaperError a d N (logarithmicRadius β d N) z):=
      (hsource z hz (hheight ▸ hfloor')).2
    have hε:0≤realSourcePaperError a d N (logarithmicRadius β d N) z:=by
      unfold realSourcePaperError
      apply inflateError_nonnegative
      exact mul_nonneg (Real.rpow_nonneg (by linarith:0≤Real.log (N:ℝ)) _)
        (baseErrorTerms_nonnegative _ _ _ _ _ hz.le)
    have hscale:scalarScale (spectralScale z) (realSourcePaperError a d N (logarithmicRadius β d N) z)≤
        (N:ℝ)^(-3*β/8):=by
      apply (scalarScale_le_sqrt (spectralScale_pos hz) hε).trans
      apply (Real.sqrt_le_sqrt (herror' z hz hheight)).trans_eq
      rw [Real.sqrt_eq_rpow,←Real.rpow_mul hNp.le]
      congr 1
      ring
    rw [←empiricalTransform_eq_finiteStieltjes g.H g.H_hermitian _ hz]
    apply hlocal.trans
    calc
      _≤(N:ℝ)^(β/8)*(N:ℝ)^(-3*β/8):=mul_le_mul hconst' hscale
        (scalarScale_nonneg hε) (Real.rpow_nonneg hNp.le _)
      _=(N:ℝ)^(-β/4):=by rw [←Real.rpow_add hNp];congr 1;ring
  have hbox:∀i,|sortedEigenvalues g.H_hermitian i|≤M:=
    fun i=>(RegularGraph.sorted_eigenvalues_box g i).trans (le_max_right _ _)
  have hCDF:=empiricalCDF_error_of_trace_sqrt (by omega) (sortedEigenvalues g.H_hermitian)
    d hd M (countingHeight β N) ((N:ℝ)^(-β/4)) (le_max_left _ _) hη hη1
    (Real.rpow_nonneg hNp.le _) hbox htrace
  intro E
  apply (hCDF E).trans
  have hsqrt:Real.sqrt (countingHeight β N)≤(N:ℝ)^(-β/4):=by
    dsimp only[countingHeight]
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hNp.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hCDFconst':T+R≤(N:ℝ)^(β/8):=by simpa only[Real.rpow_zero,mul_one] using hCDFconst
  calc
    _≤T*(N:ℝ)^(-β/4)+R*(N:ℝ)^(-β/4):=add_le_add le_rfl (mul_le_mul_of_nonneg_left hsqrt hR)
    _=(T+R)*(N:ℝ)^(-β/4):=by ring
    _≤(N:ℝ)^(β/8)*(N:ℝ)^(-β/4):=mul_le_mul_of_nonneg_right hCDFconst' (Real.rpow_nonneg hNp.le _)
    _=(N:ℝ)^(-β/8):=by rw [←Real.rpow_add hNp];congr 1;ring

end SpectralConsequences
