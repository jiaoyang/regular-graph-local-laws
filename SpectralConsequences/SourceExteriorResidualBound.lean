import SpectralConsequences.SourceExteriorScalarCaps
import SpectralConsequences.ExteriorWardScale
import SpectralConsequences.ExteriorStabilitySmallness

/-! # Actual exterior corrected trace from the two Ward-scale residuals

All spectral, depth, correction, weak-prior and numerical absorptions are
proved. The only fluctuation inputs are the explicit cavity and trace
residual inequalities that Section 7 high moments supply.
-/
open Filter
noncomputable section
set_option maxHeartbeats 1800000
namespace SpectralConsequences
open LocalLaw
local instance sourceExteriorResidualDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceExteriorFluctuationScale (a d N:ℕ) (β γ:ℝ) (z:ℂ):ℝ:=
  let ell:=actualCavityDepth a d N z-1
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let εp:=inflatedPrime (Real.log (N:ℝ)) ε
  let u:=scalarScale (spectralScale z) ε
  Real.sqrt ε*Real.sqrt ((((d-1:ℕ):ℝ)^(2*ell))*((kestenMcKayStieltjes d z).im+εp+u)/((N:ℝ)*z.im))+
    (((d-1:ℕ):ℝ)^(2*ell))*εp^2+εp/(N:ℝ)^γ

def sourceExteriorResidualConstant (d:ℕ) (B K:ℝ):ℝ:=2*K*(sourceExteriorScalarConstant d B)^3
def sourceExteriorResidualExponent (a p:ℕ):ℕ:=p+3*sourceExteriorScalarExponent a

private theorem exterior_total_log_cap (a d N p:ℕ) (B K:ℝ):
    exteriorLogCap (sourceExteriorResidualConstant d B K) (sourceExteriorResidualExponent a p) N=
      2*(K*Real.log (N:ℝ)^p)*(sourceExteriorScalarCap a d N B)^3 := by
  simp only [exteriorLogCap,sourceExteriorResidualConstant,sourceExteriorResidualExponent,sourceExteriorScalarCap]
  rw [pow_add,show 3*sourceExteriorScalarExponent a=sourceExteriorScalarExponent a*3 by omega,pow_mul,mul_pow]
  ring

theorem eventually_source_exterior_corrected_trace (a d:ℕ) (β γ e B K:ℝ) (p:ℕ)
    (ha:0<a) (hd:3≤d) (hβ:0<β) (hβsmall:β≤1/128) (hγ:9/32≤γ)
    (he:0≤e) (heβ:e<β/16) (hK:1≤K):
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(E:ℝ),2+edgeWindow β N/2≤|E|→
      let z:ℂ:=(E:ℂ)+(exteriorHeight β N:ℂ)*Complex.I
      ‖z‖≤B→
      ‖g.Q z-semicircleRoot z‖≤scalarScale (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z)→
      ‖physicalCavityFluctuation a g z‖≤K*Real.log (N:ℝ)^p*(N:ℝ)^e*sourceExteriorFluctuationScale a d N β γ z→
      ‖physicalTraceFluctuation a g z‖≤K*Real.log (N:ℝ)^p*(N:ℝ)^e*sourceExteriorFluctuationScale a d N β γ z→
      ((N:ℝ)*z.im)*‖RegularGraph.correctedSourceTrace g z-kestenMcKayStieltjes d z‖≤1/16 := by
  let Ktot:=sourceExteriorResidualConstant d B K
  let ptot:=sourceExteriorResidualExponent a p
  have hK0:1≤sourceExteriorScalarConstant d B:=by
    unfold sourceExteriorScalarConstant
    have hk:0≤((d-1:ℕ):ℝ):=Nat.cast_nonneg _
    linarith [abs_nonneg B,abs_nonneg (trivialCancellationSpectralConstant d B)]
  have hKtot:1≤Ktot:=by
    have hh:=one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hK0 (n:=3))
    dsimp only[Ktot,sourceExteriorResidualConstant]
    nlinarith only[hh]
  filter_upwards [eventually_source_exterior_scalar_caps a d β B ha hd hβ hβsmall,
    eventually_exterior_numerical_parameters β γ e Ktot ptot hβ hβsmall hγ he heβ hKtot,
    eventually_log_ge_nat 1]
    with N hcaps num hlog
  intro g E hE
  dsimp only
  let z:ℂ:=(E:ℂ)+(exteriorHeight β N:ℂ)*Complex.I
  intro hB hprior hRc hRt
  let L:=Real.log (N:ℝ)
  let x:=exteriorPower β N
  let H0:=sourceExteriorScalarCap a d N B
  let H:=exteriorLogCap Ktot ptot N
  let V:ℝ:=(N:ℝ)^e
  let ell:=actualCavityDepth a d N z-1
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let εp:=inflatedPrime L ε
  let u:=scalarScale (spectralScale z) ε
  let C0:=sourceTrivialCorrectionCap a d N z
  let gap:=sourceCorrectedGap z B
  let G:=gap⁻¹
  let Rc:=‖physicalCavityFluctuation a g z‖
  let Rt:=‖physicalTraceFluctuation a g z‖
  let cancel:=trivialCancellationSpectralConstant d B*(ell+1)*((d-1:ℕ):ℝ)^ell/
    ((N:ℝ)*Real.sqrt (spectralScale z))
  have caps:=hcaps E hE (g.Q z) hB hprior
  have hN:1≤N:=by have hh:=num.size_positive;omega
  have hNp:0<(N:ℝ):=Nat.cast_pos.mpr num.size_positive
  have hη:0<exteriorHeight β N:=Real.rpow_pos_of_pos hNp _
  have hz:0<z.im:=by simpa [z] using hη
  have hL:1≤L:=hlog
  have hH0:1≤H0:=caps.cap_one
  have hH:1≤H:=num.log_cap_one
  have hx:1≤x:=num.power_one
  have hxp:0<x:=by linarith
  have hHmom:1≤K*L^p:=one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hL)
  have hHid:H=2*(K*L^p)*H0^3:=exterior_total_log_cap a d N p B K
  have hHH:H0≤H:=by
    rw [hHid]
    have hp:H0≤H0^3:=by simpa only[pow_one] using pow_le_pow_right₀ hH0 (show 1≤3 by norm_num)
    have hmul:1≤2*(K*L^p):=by linarith only[hHmom]
    exact hp.trans (le_mul_of_one_le_left (pow_nonneg (by linarith:0≤H0) _) hmul)
  have hu:0≤u:=scalarScale_nonneg caps.error_nonnegative
  have hε:0≤ε:=caps.error_nonnegative
  have hC0:0≤C0:=by dsimp only[C0,sourceTrivialCorrectionCap];positivity
  have hG:0≤G:=inv_nonneg.mpr caps.gap_positive.le
  have huCap:u≤H/x^14:=caps.weak_scale_cap.trans (div_le_div_of_nonneg_right hHH (pow_nonneg hxp.le _))
  have hCcap:C0≤H/x^24:=caps.correction_cap.trans (div_le_div_of_nonneg_right hHH (pow_nonneg hxp.le _))
  have hGcap:G≤H*x:=caps.gap_inverse_cap.trans (mul_le_mul_of_nonneg_right hHH hxp.le)
  have hdepth:(ell:ℝ)+4≤H:=caps.depth_cap.trans hHH
  have hraw:sourceExteriorFluctuationScale a d N β γ z≤
      2*H0^3*(1/x^26+1/x^30+1/(x^15*(N:ℝ)^γ)):=by
    dsimp only[sourceExteriorFluctuationScale]
    have hscale:(N:ℝ)*z.im=x^24:=by simpa [z] using num.height_identity.symm
    rw [hscale]
    exact exterior_residual_scale_bound x H0 ε (kestenMcKayStieltjes d z).im εp u
      (((d-1:ℕ):ℝ)^(2*ell)) ((N:ℝ)^γ) hx hH0 (Real.rpow_pos_of_pos hNp _) caps.reference_nonnegative
      (by dsimp only[εp,inflatedPrime];positivity) hu caps.error_cap caps.reference_cap
      caps.prime_cap caps.weak_scale_cap caps.tree_factor_cap
  have hRcCap:Rc≤H*V*(1/x^26+1/x^30+1/(x^15*(N:ℝ)^γ)):=by
    apply hRc.trans
    have hh:=mul_le_mul_of_nonneg_left hraw (show 0≤K*L^p*V by positivity)
    exact hh.trans_eq (by rw [hHid];ring)
  have hRtCap:Rt≤H*V*(1/x^26+1/x^30+1/(x^15*(N:ℝ)^γ)):=by
    apply hRt.trans
    have hh:=mul_le_mul_of_nonneg_left hraw (show 0≤K*L^p*V by positivity)
    exact hh.trans_eq (by rw [hHid];ring)
  have hsmall:=exterior_stability_smallness x H ((ell:ℝ)+4) u C0 G hx hH hdepth hu hC0 hG huCap hCcap hGcap num.second_smallness
  have hsmall':((ell:ℝ)+1)*(u+C0*(1/gap+1))≤gap/2:=by
    have hGpos:0<G:=inv_pos.mpr caps.gap_positive
    have hsum:0≤u+C0*(G+1):=by positivity
    have hh:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show (ell:ℝ)+1≤(ell:ℝ)+4 by linarith) hsum) hG
    have hprod:(((ell:ℝ)+1)*(u+C0*(G+1)))*G≤1/2:=hh.trans hsmall.2
    apply (mul_le_mul_right hGpos).mp
    have hmul:gap*G=1:=mul_inv_cancel₀ (ne_of_gt caps.gap_positive)
    have hid:(1/2:ℝ)=(gap/2)*G:=by
      calc
        _=(gap*G)/2:=by rw [hmul]
        _=_:=by ring
    simpa only[one_div] using hprod.trans_eq hid
  have ht:=RegularGraph.actual_corrected_trace_bound_of_residuals g a hN hd z hz B hB Rc Rt u hprior
    hsmall.1 hsmall' le_rfl le_rfl
  have ht':‖RegularGraph.correctedSourceTrace g z-kestenMcKayStieltjes d z‖≤
      Rt+16*((ell:ℝ)+4)*u^2+24*Rc*G+48*((ell:ℝ)+4)*C0^2*G^3+cancel:=by
    apply ht.trans
    change Rt+16*((ell:ℝ)+4)*u^2+24*Rc/gap+48*((ell:ℝ)+1)*C0^2/gap^3+cancel≤_
    simp only[div_eq_mul_inv,←inv_pow]
    have hterm:48*((ell:ℝ)+1)*C0^2*G^3≤48*((ell:ℝ)+4)*C0^2*G^3:=by
      gcongr
      linarith
    exact add_le_add_right (add_le_add_left hterm (Rt+16*((ell:ℝ)+4)*u^2+24*Rc*G)) cancel
  have hcan:cancel≤H*x/(N:ℝ):=caps.cancellation_cap.trans (by gcongr)
  have hb:=exterior_correction_budget_bound x (N:ℝ) ((N:ℝ)^γ) H V ((ell:ℝ)+4) u Rc Rt C0 G cancel
    hx hH num.moment_one num.size_power num.exit_power hdepth hu hC0 hG huCap hCcap hGcap hRcCap hRtCap hcan
  have hscale:(N:ℝ)*z.im=x^24:=by simpa [z] using num.height_identity.symm
  rw [hscale]
  exact (mul_le_mul_of_nonneg_left ht' (pow_nonneg hxp.le _)).trans (hb.trans num.trace_absorption)

end SpectralConsequences
