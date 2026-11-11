import SpectralConsequences.RegularRootTaylor
import LocalLaw.CavityIterationContinuity

/-! Parameter changes of the actual recursion targets preserve the refined
Ward variance scale of changes in Q and the empirical trace. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SpectralConsequences
open LocalLaw

theorem regularRootValue_lipschitz_of_small (d ell:ℕ)(hd:3≤d)(u v z:ℂ)
    (hz:0<z.im)(huim:0≤u.im)(hvim:0≤v.im)
    (hu:((ell:ℝ)+4)*‖u-semicircleRoot z‖≤1/2)
    (hv:((ell:ℝ)+4)*‖v-semicircleRoot z‖≤1/2):
    ‖regularRootValue d ell u z-regularRootValue d ell v z‖≤32*‖u-v‖:=by
  let m:=semicircleRoot z
  let md:=kestenMcKayTransform d m z
  let A:=regularRootLinearCoefficient d ell m md
  let B:=m*cavitySum m ell+(d:ℂ)/((d-1:ℕ):ℂ)*md*m^(2*ell)
  let Du:=1-B*(u-m)
  let Dv:=1-B*(v-m)
  have hB:‖B‖≤(ell:ℝ)+4:=regularRootFeedbackCoefficient_bound d ell hd z hz
  have hBu:‖B*(u-m)‖≤1/2:=by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hB (norm_nonneg _)).trans hu
  have hBv:‖B*(v-m)‖≤1/2:=by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hB (norm_nonneg _)).trans hv
  have hDu:1/2≤‖Du‖:=by
    have hh:=norm_sub_norm_le (1:ℂ) (B*(u-m))
    simp only [norm_one] at hh
    change 1/2≤‖1-B*(u-m)‖
    linarith
  have hDv:1/2≤‖Dv‖:=by
    have hh:=norm_sub_norm_le (1:ℂ) (B*(v-m))
    simp only [norm_one] at hh
    change 1/2≤‖1-B*(v-m)‖
    linarith
  have hDu0:Du≠0:=norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hDu)
  have hDv0:Dv≠0:=norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hDv)
  have hprioru:(ell:ℝ)*‖u-m‖≤1/2:=by nlinarith [norm_nonneg (u-m)]
  have hpriorv:(ell:ℝ)*‖v-m‖≤1/2:=by nlinarith [norm_nonneg (v-m)]
  have hXu:=regularRootValue_exact d ell m u z (semicircleRoot_equation z) hz huim
    (semicircleRoot_im_pos hz).le (cavityDenominator_all_ne_zero (semicircleRoot_norm_le_one z) ell hprioru)
  have hXv:=regularRootValue_exact d ell m v z (semicircleRoot_equation z) hz hvim
    (semicircleRoot_im_pos hz).le (cavityDenominator_all_ne_zero (semicircleRoot_norm_le_one z) ell hpriorv)
  change regularRootValue d ell u z-md=A*(u-m)/Du at hXu
  change regularRootValue d ell v z-md=A*(v-m)/Dv at hXv
  have hex:regularRootValue d ell u z-regularRootValue d ell v z=A*(u-v)/(Du*Dv):=by
    calc
      _=(regularRootValue d ell u z-md)-(regularRootValue d ell v z-md):=by ring
      _=_:=by
        rw [hXu,hXv]
        field_simp [hDu0,hDv0]
        dsimp only [Du,Dv]
        ring
  have hden:1/4≤‖Du‖*‖Dv‖:=by nlinarith only [hDu,hDv]
  have hdenpos:0<‖Du‖*‖Dv‖:=by linarith
  rw [hex,norm_div,norm_mul,norm_mul]
  have hnum:=mul_le_mul_of_nonneg_right (regularRootLinearCoefficient_norm_le_eight d ell hd z hz) (norm_nonneg (u-v))
  apply (div_le_iff₀ hdenpos).mpr
  have hmult:=mul_le_mul_of_nonneg_left hden (norm_nonneg (u-v))
  nlinarith only [hnum,hmult]

theorem corrected_cavity_residual_change {m z u v:ℂ}(hm:m^2+z*m+1=0)(hmnorm:‖m‖≤1)
    (n:ℕ)(hu:(n:ℝ)*‖u-m‖≤1/2)(hv:(n:ℝ)*‖v-m‖≤1/2)(c:ℂ):
    ‖(u-cavityIterate z u n-c)-(v-cavityIterate z v n-c)‖≤5*‖u-v‖:=by
  have hEq:(u-cavityIterate z u n-c)-(v-cavityIterate z v n-c)=
      (u-v)-(cavityIterate z u n-cavityIterate z v n):=by ring
  rw [hEq]
  have hh:=cavityIterate_lipschitz_of_small hm hmnorm n hu hv
  exact (norm_sub_le _ _).trans (by linarith)

theorem corrected_trace_residual_change (d ell:ℕ)(hd:3≤d)(u v s t c z:ℂ)
    (hz:0<z.im)(huim:0≤u.im)(hvim:0≤v.im)
    (hu:((ell:ℝ)+4)*‖u-semicircleRoot z‖≤1/2)
    (hv:((ell:ℝ)+4)*‖v-semicircleRoot z‖≤1/2):
    ‖(s-regularRootValue d ell u z-c)-(t-regularRootValue d ell v z-c)‖≤
      ‖s-t‖+32*‖u-v‖:=by
  have hEq:(s-regularRootValue d ell u z-c)-(t-regularRootValue d ell v z-c)=
      (s-t)-(regularRootValue d ell u z-regularRootValue d ell v z):=by ring
  rw [hEq]
  exact (norm_sub_le _ _).trans (add_le_add_left
    (regularRootValue_lipschitz_of_small d ell hd u v z hz huim hvim hu hv) _)

end SpectralConsequences
