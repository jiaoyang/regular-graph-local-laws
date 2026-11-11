import SpectralConsequences.CorrectedCavityStability
import SpectralConsequences.RegularRootTaylor
import SpectralConsequences.TrivialCorrectionSpectral
import LocalLaw.KestenMcKayStieltjes

/-! The corrected trace follows from the two actual fluctuation residuals.
All scalar and finite-tree algebra is discharged in the theorem below. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace SpectralConsequences
open LocalLaw

theorem corrected_trace_linearization (s X md q m A cQ cM pole T:ℂ)
    (Rt RX RQ Rcorr Amax:ℝ)
    (ht:‖s-X-cM‖≤Rt)(hX:‖X-md-A*(q-m)‖≤RX)
    (hq:‖q-m-cQ/T‖≤RQ)(hc:‖cM+A/T*cQ-pole‖≤Rcorr)
    (hA:‖A‖≤Amax):
    ‖s-md-pole‖≤Rt+RX+Amax*RQ+Rcorr:=by
  have hRQ:0≤RQ:=(norm_nonneg _).trans hq
  have heq:s-md-pole=(s-X-cM)+(X-md-A*(q-m))+A*(q-m-cQ/T)+(cM+A/T*cQ-pole):=by ring
  rw [heq]
  calc
    _≤(‖s-X-cM‖+‖X-md-A*(q-m)‖)+‖A*(q-m-cQ/T)‖+‖cM+A/T*cQ-pole‖:=by
      exact (norm_add_le _ _).trans (add_le_add_right
        ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)) _)
    _≤Rt+RX+Amax*RQ+Rcorr:=by
      apply add_le_add _ hc
      apply add_le_add (add_le_add ht hX)
      rw [norm_mul]
      exact mul_le_mul hA hq (norm_nonneg _) ((norm_nonneg _).trans hA)

theorem corrected_cavity_bound_of_gap {m q z:ℂ}(hm:m^2+z*m+1=0)(hmnorm:‖m‖≤1)
    (n:ℕ)(c:ℂ)(Rc u C0 g:ℝ)(hg:0<g)(hgap:g≤‖1-m^(2*n)‖)
    (hprior:‖q-m‖≤u)(hc:‖c‖≤C0)(hpriorSmall:(n:ℝ)*u≤1/2)
    (hsmall:(n:ℝ)*(u+C0*(1/g+1))≤g/2)
    (hres:‖q-cavityIterate z q n-c‖≤Rc):
    ‖q-m-c/(1-m^(2*n))‖≤3*Rc/g+6*(n:ℝ)*C0^2/g^3:=by
  let T:=1-m^(2*n)
  have ht:0<‖T‖:=lt_of_lt_of_le hg hgap
  have hT:T≠0:=norm_pos_iff.mp ht
  have hn:0≤(n:ℝ):=Nat.cast_nonneg n
  have hu:0≤u:=(norm_nonneg _).trans hprior
  have hC:0≤C0:=(norm_nonneg _).trans hc
  have hR:0≤Rc:=(norm_nonneg _).trans hres
  have ha:‖m*cavitySum m n‖≤(n:ℝ):=by
    rw [norm_mul]
    exact (mul_le_mul hmnorm (cavitySum_norm_le hmnorm n) (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  have hrecip:1/‖T‖≤1/g:=one_div_le_one_div_of_le hg hgap
  have hsmall':‖m*cavitySum m n‖*(‖q-m‖+‖c‖*(1/‖T‖+1))≤‖T‖/2:=by
    apply (mul_le_mul ha (add_le_add hprior
      (mul_le_mul hc (add_le_add_right hrecip 1) (by positivity) hC)) (by positivity) hn).trans
    exact hsmall.trans (div_le_div_of_nonneg_right hgap (by norm_num))
  have hbase:=corrected_cavity_stability hm hmnorm n
    ((mul_le_mul_of_nonneg_left hprior hn).trans hpriorSmall) c Rc hT hres hsmall'
  apply hbase.trans
  have htupper:‖T‖≤2:=by
    have hp:‖m^(2*n)‖≤1:=by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg m) hmnorm
    have hh:=norm_sub_le (1:ℂ) (m^(2*n))
    simp only [norm_one] at hh
    change ‖1-m^(2*n)‖≤2
    linarith
  apply add_le_add
  · exact div_le_div_of_nonneg_left (by positivity) hg hgap
  · have hnum:2*‖m*cavitySum m n‖*‖c‖^2*(1+‖T‖)≤6*(n:ℝ)*C0^2:=by
      have hsq:‖c‖^2≤C0^2:=sq_le_sq₀ (norm_nonneg c) hC |>.mpr hc
      have hh:=mul_le_mul (mul_le_mul_of_nonneg_left ha (by norm_num:0≤(2:ℝ))) hsq (sq_nonneg _) (by positivity)
      have hh':=mul_le_mul hh (show 1+‖T‖≤3 by linarith) (by positivity) (by positivity)
      nlinarith
    exact div_le_div₀ (by positivity) hnum (by positivity) (pow_le_pow_left₀ hg.le hgap 3)

theorem corrected_trace_bound_of_residuals (N d ell:ℕ)(hN:1≤N)(hd:3≤d)
    (z q s:ℂ)(hz:0<z.im)(hq:0≤q.im)(B:ℝ)(hB:‖z‖≤B)
    (hn:1/2≤‖cavitySum (semicircleRoot z) (ell+1)‖)
    (Rc Rt u C0 g:ℝ)(hg:0<g)
    (hgap:g≤‖1-(semicircleRoot z)^(2*ell+2)‖)
    (hprior:‖q-semicircleRoot z‖≤u)
    (hc:‖trivialCavityCorrection N d ell z‖≤C0)
    (hpriorSmall:((ell:ℝ)+4)*u≤1/2)
    (hsmall:((ell:ℝ)+1)*(u+C0*(1/g+1))≤g/2)
    (hresQ:‖q-cavityIterate z q (ell+1)-trivialCavityCorrection N d ell z‖≤Rc)
    (hresTrace:‖s-regularRootValue d ell q z-trivialTraceCorrection N d ell z‖≤Rt):
    ‖s-kestenMcKayStieltjes d z-trivialPole N d z‖≤
      Rt+16*((ell:ℝ)+4)*u^2+24*Rc/g+48*((ell:ℝ)+1)*C0^2/g^3+
        trivialCancellationSpectralConstant d B*(ell+1)*((d-1:ℕ):ℝ)^ell/
          ((N:ℝ)*Real.sqrt (spectralScale z)):=by
  have hu:0≤u:=(norm_nonneg _).trans hprior
  have hsmallQ:((ell+1:ℕ):ℝ)*u≤1/2:=by push_cast; nlinarith
  have hsmallX:((ell:ℝ)+4)*‖q-semicircleRoot z‖≤1/2:=
    (mul_le_mul_of_nonneg_left hprior (by positivity)).trans hpriorSmall
  have hgap':g≤‖1-(semicircleRoot z)^(2*(ell+1))‖:=by
    simpa only [Nat.mul_add,Nat.mul_one] using hgap
  have hsmall':((ell+1:ℕ):ℝ)*(u+C0*(1/g+1))≤g/2:=by
    simpa only [Nat.cast_add,Nat.cast_one] using hsmall
  have hQ:=corrected_cavity_bound_of_gap (semicircleRoot_equation z)
    (semicircleRoot_norm_le_one z) (ell+1) (trivialCavityCorrection N d ell z)
    Rc u C0 g hg hgap' hprior hc hsmallQ hsmall' hresQ
  have hQ':‖q-semicircleRoot z-trivialCavityCorrection N d ell z/
      (1-(semicircleRoot z)^(2*ell+2))‖≤3*Rc/g+6*((ell:ℝ)+1)*C0^2/g^3:=by
    simpa only [Nat.mul_add,Nat.mul_one,Nat.cast_add,Nat.cast_one] using hQ
  have hX:=regularRootValue_taylor_bound d ell hd q z hz hq hsmallX
  have hsq:‖q-semicircleRoot z‖^2≤u^2:=sq_le_sq₀ (norm_nonneg _) hu |>.mpr hprior
  have hX':‖regularRootValue d ell q z-kestenMcKayTransform d (semicircleRoot z) z-
      regularRootLinearCoefficient d ell (semicircleRoot z)
        (kestenMcKayTransform d (semicircleRoot z) z)*(q-semicircleRoot z)‖≤
      16*((ell:ℝ)+4)*u^2:=hX.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
  have hh:=corrected_trace_linearization s (regularRootValue d ell q z)
    (kestenMcKayTransform d (semicircleRoot z) z) q (semicircleRoot z)
    (regularRootLinearCoefficient d ell (semicircleRoot z) (kestenMcKayTransform d (semicircleRoot z) z))
    (trivialCavityCorrection N d ell z) (trivialTraceCorrection N d ell z)
    (trivialPole N d z) (1-(semicircleRoot z)^(2*ell+2))
    Rt (16*((ell:ℝ)+4)*u^2) (3*Rc/g+6*((ell:ℝ)+1)*C0^2/g^3)
    (trivialCancellationSpectralConstant d B*(ell+1)*((d-1:ℕ):ℝ)^ell/
      ((N:ℝ)*Real.sqrt (spectralScale z))) 8
    hresTrace hX' hQ' (trivial_correction_cancellation_spectral N d ell hN hd z hz B hB hn)
    (regularRootLinearCoefficient_norm_le_eight d ell hd z hz)
  rw [kestenMcKayStieltjes_eq_transform d hd z hz]
  exact hh.trans_eq (by ring)

end SpectralConsequences
