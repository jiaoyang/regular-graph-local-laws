import SpectralConsequences.SourceMomentRecurrence
import SpectralConsequences.SourceHighMomentBounds
import SpectralConsequences.ThreeTermFluctuationBound
import SpectralConsequences.MomentExceptionAbsorption

/-! Genuine high moments of both physical Section7 residuals. The proof
instantiates the actual reversible recurrence and absorbs its true lower
moments. No moment or tail estimate is a hypothesis. -/
open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2800000
namespace SpectralConsequences
open LocalLaw
local instance sourceActualHighMomentsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem source_actual_high_moment_bounds (a b d:ℕ)(c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hc1:c≤1/16)
    (hβ:0<β)(hβc:β≤c/32)(hB:2*(d:ℝ)≤B):
    SourceHighMomentBounds a b d c β B:=by
  intro p hp
  let m:=6*a+7
  let Kd:=|sourceTraceDriftConstant d β B|+2
  let Kl:=sourceLocalObservableChangeConstant d β B
  let I:=momentIncrementCoefficient p
  let H:=8*(I+1)
  let C:=H*(Kd+Kl+1)
  let D:=4*p+1
  have hB0:0≤B:=by have hh:=(Nat.cast_le (α:=ℝ)).mpr hd;linarith
  have hKd:1≤Kd:=by dsimp only [Kd];linarith [abs_nonneg (sourceTraceDriftConstant d β B)]
  have hKl:1≤Kl:=by
    have hh:0≤oldTreeRootErrorConstant d β B:=by
      dsimp only [oldTreeRootErrorConstant,oldTreeFormalConstant];positivity
    dsimp only [Kl,sourceLocalObservableChangeConstant];linarith
  have hI:0≤I:=by dsimp only [I,momentIncrementCoefficient];positivity
  have hH:8≤H:=by dsimp only [H];linarith
  have hHI:8*I≤H:=by dsimp only [H];linarith
  have hC:1≤C:=by dsimp only [C];nlinarith
  refine ⟨C,hC,m+1,?_⟩
  have hβ1:β≤1:=by linarith
  have hJgap:2*β<(9/32:ℝ):=by linarith
  have hDgap:((4*p:ℕ):ℝ)*β<(D:ℝ):=by
    dsimp only [D]
    push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) p]
  filter_upwards [eventually_source_moment_recurrence a b d p D c β B ha hb hd (by omega) hc hc1 hβ hβc hB,
    eventually_source_moment_variance_small a b d β (sourceWardVarianceConstant d B) ha hb hd hβ
      (sourceWardVarianceConstant_nonnegative d B hd hB0),
    eventually_moment_exception_absorbed a d 0 0 2 β (9/32) (sourceMomentLocalChangeCap d B) hd hβ.le hJgap,
    eventually_moment_exception_absorbed a d 0 0 (4*p) β (D:ℝ) (sourceMomentExceptionConstant d p B) hd hβ.le hDgap,
    eventually_log_ge_nat 1,eventually_ge_atTop 1]
    with N hrec hvar hJ hE hlog hN
  intro z hz hzB hfloor cavity
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let V:=sourceMomentVariance a d N (logarithmicRadius β d N) (sourceWardVarianceConstant d B) z
  let S:=sourceHighMomentScale a d N β B z
  let U:=Kl*L*ε
  let B0:=Kd*L^m*ε^2
  let E0:=sourceMomentExceptionConstant d p B/(N:ℝ)^D
  let ell:=actualCavityDepth a d N z-1
  let Ω:=momentSourceEvent N d a c β z
  let F:=fun g:RegularGraph N d=>momentResidual cavity g ell z
  let w:=fun g:RegularGraph N d=>if Ω g then RegularGraph.weight g else 0
  have hL:1≤L:=hlog
  have hL0:0≤L:=by linarith
  have hε:0≤ε:=graphPaperError_nonnegative _ _ _ _ _ hN hz.le
  have hV:0≤V:=(hvar z hz hfloor).1.1
  have hVε:V≤ε:=(hvar z hz hfloor).1.2.2
  have hU:0≤U:=by dsimp only [U];positivity
  have hVU:V≤U:=hVε.trans (by
    have hh:1≤Kl*L:=one_le_mul_of_one_le_of_one_le hKl hL
    exact le_mul_of_one_le_left hε hh)
  have hB0:0≤B0:=by dsimp only [B0];positivity
  have hS:0≤S:=sourceHighMomentScale_nonnegative _ _ _ _ _ _
  have hSε:ε^2≤S:=le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hSsqrt:Real.sqrt (ε*V)≤S:=le_add_of_nonneg_left (sq_nonneg ε)
  have hLm:1≤L^m:=one_le_pow₀ hL
  have hbase:ε^2≤B0:=by
    have hh:1≤Kd*L^m:=one_le_mul_of_one_le_of_one_le hKd hLm
    exact le_mul_of_one_le_left (sq_nonneg ε) hh
  have hE0:E0≤B0^(2*p):=by
    have he':E0≤ε^(4*p):=by
      simpa only [pow_zero,mul_one,div_one,Real.rpow_natCast] using hE z hz.le
    apply he'.trans
    have hh:=pow_le_pow_left₀ (sq_nonneg ε) hbase (2*p)
    simpa only [←pow_mul,show 2*(2*p)=4*p by omega] using hh
  have hJ':sourceMomentLocalChangeCap d B/(N:ℝ)^(9/32:ℝ)≤ε^2:=by
    simpa only [pow_zero,mul_one,div_one] using hJ z hz.le
  have hcoeff:sourceTraceDriftConstant d β B*L^m*ε^2+
      sourceMomentLocalChangeCap d B/(N:ℝ)^(9/32:ℝ)+ε^2≤B0:=by
    have ht:=mul_le_mul_of_nonneg_right (le_abs_self (sourceTraceDriftConstant d β B))
      (show 0≤L^m*ε^2 by positivity)
    have hl:=mul_le_mul_of_nonneg_right hLm (sq_nonneg ε)
    dsimp only [B0,Kd]
    nlinarith only [hJ',ht,hl]
  have hweight:∀g:RegularGraph N d,0≤w g:=by intro g;dsimp only [w];split_ifs;exact RegularGraph.weight_nonnegative g;rfl
  have hmass:(∑g:RegularGraph N d,w g)≤1:=by
    apply (event_weight_subprobability (RegularGraph.weight (N:=N) (d:=d))
      RegularGraph.weight_nonnegative ?_ Ω).2
    by_cases hne:Nonempty (RegularGraph N d)
    · letI:=hne;rw [RegularGraph.weight_normalized]
    · letI:IsEmpty (RegularGraph N d):=not_nonempty_iff.mp hne
      simp
  have hlower (n:ℕ):sourceMomentLower N d a c β cavity ell z n=∑g:RegularGraph N d,w g*‖F g‖^n:=by
    simp only [sourceMomentLower,w,F,Ω,ite_mul,zero_mul]
  have hrec':(∑g:RegularGraph N d,w g*‖F g‖^(2*p))≤
      B0*(∑g:RegularGraph N d,w g*‖F g‖^(2*p-1))+
      (I*U*V)*(∑g:RegularGraph N d,w g*‖F g‖^(2*p-2))+I*U*V^(2*p-1)+E0:=by
    have hh:truncatedMoment (RegularGraph.weight (N:=N) (d:=d)) Ω F p≤
        (sourceTraceDriftConstant d β B*L^m*ε^2+sourceMomentLocalChangeCap d B/(N:ℝ)^(9/32:ℝ)+ε^2)*
          sourceMomentLower N d a c β cavity ell z (2*p-1)+
        I*U*V*sourceMomentLower N d a c β cavity ell z (2*p-2)+I*U*V^(2*p-1)+E0:=
      hrec z hz hzB hfloor cavity
    rw [hlower (2*p-1),hlower (2*p-2)] at hh
    have hlow:0≤∑g:RegularGraph N d,w g*‖F g‖^(2*p-1):=
      Finset.sum_nonneg (fun g _=>mul_nonneg (hweight g) (by positivity))
    have hc:=mul_le_mul_of_nonneg_right hcoeff hlow
    have he:truncatedMoment (RegularGraph.weight (N:=N) (d:=d)) Ω F p=
        ∑g:RegularGraph N d,w g*‖F g‖^(2*p):=by simp only [truncatedMoment,w,ite_mul,zero_mul]
    rw [he] at hh
    exact hh.trans (add_le_add_right (add_le_add_right (add_le_add_right hc _) _) _)
  have hmoment:=three_term_fluctuation_bound w (fun g=>‖F g‖) hweight (fun g=>norm_nonneg _) hmass
    (2*p) (by omega) B0 I U V E0 H hB0 hI hU hV hVU hE0 hH hHI hrec'
  have hsqrt:Real.sqrt (U*V)≤(Kl+1)*L*Real.sqrt (ε*V):=by
    have hc:Real.sqrt (Kl*L)≤(Kl+1)*L:=by
      have hh:Real.sqrt (Kl*L)≤Kl*L+1:=by
        apply Real.sqrt_le_iff.mpr
        exact ⟨by positivity,by nlinarith [sq_nonneg (Kl*L)]⟩
      exact hh.trans (by nlinarith only [hL])
    rw [show U*V=(Kl*L)*(ε*V) by dsimp only [U];ring,Real.sqrt_mul (by positivity)]
    exact mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)
  have hLm':L^m≤L^(m+1):=pow_le_pow_right₀ hL (by omega)
  have hL':L≤L^(m+1):=by simpa only [pow_one] using pow_le_pow_right₀ hL (show 1 ≤ m+1 by omega)
  have hBscale:B0≤Kd*L^(m+1)*S:=by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hLm' (by linarith:(0:ℝ)≤Kd)) hSε (sq_nonneg ε) (by positivity)
  have hrootscale:Real.sqrt (U*V)≤(Kl+1)*L^(m+1)*S:=
    hsqrt.trans (mul_le_mul (mul_le_mul_of_nonneg_left hL' (by linarith:(0:ℝ)≤Kl+1)) hSsqrt
      (Real.sqrt_nonneg _) (by positivity))
  have hthreshold:H*(B0+Real.sqrt (U*V))≤C*L^(m+1)*S:=by
    have hh:=mul_le_mul_of_nonneg_left (add_le_add hBscale hrootscale) (by linarith:(0:ℝ)≤H)
    convert hh using 1;dsimp only [C];ring
  have hfinal:=hmoment.trans (pow_le_pow_left₀ (by positivity) hthreshold (2*p))
  simpa only [truncatedMoment,w,Ω,F,ell,ite_mul,zero_mul,L,S] using hfinal

end SpectralConsequences
