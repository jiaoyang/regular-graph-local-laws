import LocalLaw.WeightedAsymmetricCoreError

/-! # Asymmetric restoration keeps the actual harmonic L1 weights

The uniform core error pays the two true L1 weights. The residual harmonic
coefficients pay the uniform core cap and one finite index count. Only the
decaying localization tail uses the square of that count.
-/

open scoped BigOperators
namespace LocalLaw

theorem product_le_envelope_with_residual (x y A B s:ℝ)
    (hx:0≤x)(hy:0≤y)(hA:0≤A)(hB:0≤B)(hs:0≤s)
    (hxa:x≤A+s)(hyb:y≤B+s) : x*y≤A*B+s*(x+y) := by
  by_cases hxs:x≤s
  · have hh:=mul_le_mul_of_nonneg_right hxs hy
    nlinarith only [hh,mul_nonneg hA hB,mul_nonneg hs hx]
  · by_cases hys:y≤s
    · have hh:=mul_le_mul_of_nonneg_left hys hx
      nlinarith only [hh,mul_nonneg hA hB,mul_nonneg hs hy]
    · have hh:=mul_le_mul (show x-s≤A by linarith) (show y-s≤B by linarith)
        (show 0≤y-s by linarith) hA
      nlinarith only [hh,sq_nonneg s]

theorem weighted_asymmetric_core_term_l1 (a e b:ℂ)(ρ K s δ v C:ℝ)
    (hρ:0≤ρ)(hρone:ρ≤1)(hK:0≤K)(hs:0≤s)(hδ:0≤δ)(hv:0≤v)(hC:0≤C)
    (r ri rj di dj:ℕ)(hri:r≤ri+di)(hrj:r≤rj+dj)
    (ha:‖a‖≤K*ρ^di+s)(hb:‖b‖≤K*ρ^dj+s)
    (he:‖e‖≤δ+v*ρ^(ri+rj))(hecap:‖e‖≤C) :
    ‖a*e*b‖≤δ*‖a‖*‖b‖+K^2*v*ρ^(2*r)+C*s*(‖a‖+‖b‖) := by
  have hi:0≤ρ^di:=pow_nonneg hρ _
  have hj:0≤ρ^dj:=pow_nonneg hρ _
  have ht:0≤v*ρ^(ri+rj):=mul_nonneg hv (pow_nonneg hρ _)
  have hp:=product_le_envelope_with_residual ‖a‖ ‖b‖ (K*ρ^di) (K*ρ^dj) s
    (norm_nonneg _) (norm_nonneg _) (mul_nonneg hK hi) (mul_nonneg hK hj) hs ha hb
  have htail:ρ^di*ρ^dj*ρ^(ri+rj)≤ρ^(2*r):=by
    rw [←pow_add,←pow_add]
    exact pow_le_pow_of_le_one hρ hρone (by omega)
  have htailScaled:K^2*(v*(ρ^di*ρ^dj*ρ^(ri+rj)))≤K^2*v*ρ^(2*r):=by
    have hh:=mul_le_mul_of_nonneg_left htail (mul_nonneg (sq_nonneg K) hv)
    nlinarith only [hh]
  rw [norm_mul,norm_mul]
  by_cases heδ:‖e‖≤δ
  · have hh:=mul_le_mul_of_nonneg_left heδ (mul_nonneg (norm_nonneg a) (norm_nonneg b))
    have hr0:0≤K^2*v*ρ^(2*r)+C*s*(‖a‖+‖b‖):=by positivity
    nlinarith only [hh,hr0]
  · have hres:0≤‖e‖-δ:=by linarith
    have hrem:‖e‖-δ≤v*ρ^(ri+rj):=by linarith
    have hmain:((K*ρ^di)*(K*ρ^dj))*(‖e‖-δ)≤K^2*v*ρ^(2*r):=by
      have hh:=mul_le_mul_of_nonneg_left hrem (show 0≤(K*ρ^di)*(K*ρ^dj) by positivity)
      exact hh.trans (by nlinarith only [htailScaled])
    have hsmall:s*(‖a‖+‖b‖)*(‖e‖-δ)≤C*s*(‖a‖+‖b‖):=by
      have hh:=mul_le_mul_of_nonneg_left (show ‖e‖-δ≤C by linarith)
        (show 0≤s*(‖a‖+‖b‖) by positivity)
      nlinarith only [hh]
    have hh:=mul_le_mul_of_nonneg_right hp hres
    nlinarith only [hh,hmain,hsmall]

theorem weighted_asymmetric_core_sum_l1 {I:Type*} [Fintype I]
    (a b:I→ℂ)(E:Matrix I I ℂ)(ρ K s δ v C A B:ℝ)
    (hρ:0≤ρ)(hρone:ρ≤1)(hK:0≤K)(hs:0≤s)(hδ:0≤δ)(hv:0≤v)(hC:0≤C)(hA:0≤A)(hB:0≤B)
    (r:ℕ)(ri di dj:I→ℕ)(hri:∀i,r≤ri i+di i)(hrj:∀j,r≤ri j+dj j)
    (ha:∀i,‖a i‖≤K*ρ^(di i)+s)(hb:∀j,‖b j‖≤K*ρ^(dj j)+s)
    (he:∀i j,‖E i j‖≤δ+v*ρ^(ri i+ri j))(hecap:∀i j,‖E i j‖≤C)
    (hleft:(∑i,‖a i‖)≤A)(hright:(∑i,‖b i‖)≤B) :
    ‖∑i,∑j,a i*E i j*b j‖≤δ*A*B+(Fintype.card I:ℝ)^2*K^2*v*ρ^(2*r)+
      C*s*(Fintype.card I:ℝ)*(A+B) := by
  have hp (i j:I):‖a i*E i j*b j‖≤δ*‖a i‖*‖b j‖+K^2*v*ρ^(2*r)+C*s*(‖a i‖+‖b j‖):=
    weighted_asymmetric_core_term_l1 (a i) (E i j) (b j) ρ K s δ v C hρ hρone hK hs hδ hv hC
      r (ri i) (ri j) (di i) (dj j) (hri i) (hrj j) (ha i) (hb j) (he i j) (hecap i j)
  have hprod:δ*(∑i,‖a i‖)*(∑j,‖b j‖)≤δ*A*B:=by
    have hh:=mul_le_mul hleft hright (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hA
    nlinarith only [mul_le_mul_of_nonneg_left hh hδ]
  have hsum:C*s*(Fintype.card I:ℝ)*((∑i,‖a i‖)+(∑j,‖b j‖))≤C*s*(Fintype.card I:ℝ)*(A+B):=
    mul_le_mul_of_nonneg_left (add_le_add hleft hright) (by positivity)
  calc
    _≤∑i,∑j,‖a i*E i j*b j‖:=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _=>norm_sum_le _ _))
    _≤∑i,∑j,(δ*‖a i‖*‖b j‖+K^2*v*ρ^(2*r)+C*s*(‖a i‖+‖b j‖)):=
      Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>hp i j))
    _=δ*(∑i,‖a i‖)*(∑j,‖b j‖)+(Fintype.card I:ℝ)^2*K^2*v*ρ^(2*r)+
        C*s*(Fintype.card I:ℝ)*((∑i,‖a i‖)+(∑j,‖b j‖)):=by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul,
        Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring
    _≤_:=add_le_add (add_le_add_right hprod _) hsum

end LocalLaw
