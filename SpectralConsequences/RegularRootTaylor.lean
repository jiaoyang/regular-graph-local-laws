import SpectralConsequences.RegularRootRecursion
import LocalLaw.ReferenceBounds

/-! Quantitative source (2.15), with every denominator controlled explicitly. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem regularRootLinearCoefficient_norm_le_eight (d ell:ℕ)(hd:3≤d)(z:ℂ)(hz:0<z.im):
    ‖regularRootLinearCoefficient d ell (semicircleRoot z) (kestenMcKayTransform d (semicircleRoot z) z)‖≤8:=by
  have hkR:2≤((d-1:ℕ):ℝ):=by exact_mod_cast (show 2≤d-1 by omega)
  have hratio:‖(d:ℂ)/((d-1:ℕ):ℂ)‖≤2:=by
    rw [norm_div,Complex.norm_natCast,Complex.norm_natCast]
    apply (div_le_iff₀ (by linarith:0<((d-1:ℕ):ℝ))).2
    have hc:((d-1:ℕ):ℝ)=(d:ℝ)-1:=by rw [Nat.cast_sub (by omega:1≤d),Nat.cast_one]
    rw [hc]
    have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
    linarith
  have hp:=kestenMcKayTransform_norm_le_two d hd z hz
  have hp2:‖kestenMcKayTransform d (semicircleRoot z) z‖^2≤4:=by nlinarith [norm_nonneg (kestenMcKayTransform d (semicircleRoot z) z)]
  unfold regularRootLinearCoefficient
  rw [norm_mul,norm_mul,norm_pow,norm_pow]
  have hh:=mul_le_mul hratio hp2 (sq_nonneg _) (by norm_num)
  exact (mul_le_mul hh (pow_le_one₀ (norm_nonneg _) (semicircleRoot_norm_le_one z)) (by positivity) (by norm_num)).trans_eq (by ring)

theorem regularRootFeedbackCoefficient_bound (d ell:ℕ)(hd:3≤d)(z:ℂ)(hz:0<z.im):
    ‖semicircleRoot z*cavitySum (semicircleRoot z) ell+
      (d:ℂ)/((d-1:ℕ):ℂ)*kestenMcKayTransform d (semicircleRoot z) z*(semicircleRoot z)^(2*ell)‖≤(ell:ℝ)+4:=by
  have hkR:2≤((d-1:ℕ):ℝ):=by exact_mod_cast (show 2≤d-1 by omega)
  have hratio:‖(d:ℂ)/((d-1:ℕ):ℂ)‖≤2:=by
    rw [norm_div,Complex.norm_natCast,Complex.norm_natCast]
    apply (div_le_iff₀ (by linarith:0<((d-1:ℕ):ℝ))).2
    have hc:((d-1:ℕ):ℝ)=(d:ℝ)-1:=by rw [Nat.cast_sub (by omega:1≤d),Nat.cast_one]
    rw [hc]
    have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
    linarith
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul,norm_mul,norm_pow]
  apply add_le_add
  · exact (mul_le_mul (semicircleRoot_norm_le_one z) (cavitySum_norm_le (semicircleRoot_norm_le_one z) ell) (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  · exact (mul_le_mul (mul_le_mul hratio (kestenMcKayTransform_norm_le_two d hd z hz) (norm_nonneg _) (by norm_num))
      (pow_le_one₀ (norm_nonneg _) (semicircleRoot_norm_le_one z)) (by positivity) (by norm_num)).trans_eq (by ring)

theorem regularRootValue_taylor_bound (d ell:ℕ)(hd:3≤d)(q z:ℂ)(hz:0<z.im)(hq:0≤q.im)
    (hsmall:((ell:ℝ)+4)*‖q-semicircleRoot z‖≤1/2):
    ‖regularRootValue d ell q z-kestenMcKayTransform d (semicircleRoot z) z-
      regularRootLinearCoefficient d ell (semicircleRoot z) (kestenMcKayTransform d (semicircleRoot z) z)*(q-semicircleRoot z)‖≤
      16*((ell:ℝ)+4)*‖q-semicircleRoot z‖^2:=by
  let m:=semicircleRoot z
  let md:=kestenMcKayTransform d m z
  let A:=regularRootLinearCoefficient d ell m md
  let B:=m*cavitySum m ell+(d:ℂ)/((d-1:ℕ):ℂ)*md*m^(2*ell)
  let δ:=q-m
  have hA:‖A‖≤8:=regularRootLinearCoefficient_norm_le_eight d ell hd z hz
  have hB:‖B‖≤(ell:ℝ)+4:=regularRootFeedbackCoefficient_bound d ell hd z hz
  have hprod:‖B*δ‖≤1/2:=by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hB (norm_nonneg δ)).trans hsmall
  have hElow:1/2≤‖1-B*δ‖:=by
    have hh:=norm_sub_norm_le (1:ℂ) (B*δ)
    simp only [norm_one] at hh
    linarith
  have hE:1-B*δ≠0:=norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hElow)
  have hprior:(ell:ℝ)*‖δ‖≤1/2:=by nlinarith [norm_nonneg δ]
  have hex:=regularRootValue_exact d ell m q z (semicircleRoot_equation z) hz hq
    (semicircleRoot_im_pos hz).le (cavityDenominator_all_ne_zero (semicircleRoot_norm_le_one z) ell hprior)
  change regularRootValue d ell q z-md=A*δ/(1-B*δ) at hex
  have hrem:regularRootValue d ell q z-md-A*δ=A*B*δ^2/(1-B*δ):=by
    rw [hex]
    field_simp [hE]
    ring
  change ‖regularRootValue d ell q z-md-A*δ‖≤_
  rw [hrem,norm_div,norm_mul,norm_mul,norm_pow]
  calc
    _≤(8*((ell:ℝ)+4)*‖δ‖^2)/(1/2):=
      div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_right (mul_le_mul hA hB (norm_nonneg B) (by norm_num)) (sq_nonneg ‖δ‖))
        (by norm_num) hElow
    _=16*((ell:ℝ)+4)*‖δ‖^2:=by ring

end SpectralConsequences
#print axioms SpectralConsequences.regularRootValue_taylor_bound
