import LocalLaw.CoreSchurLift

/-! # Harmonic restoration weights recover the two target radii

The small residual part of a harmonic coefficient pays a uniform core cap;
it does not multiply the sample count in the localization tail. The main
decaying coefficients recover every lost secondary-endpoint radius.
-/

open scoped BigOperators
namespace LocalLaw

theorem weighted_asymmetric_core_term (a e b:ℂ)(ρ K s δ v C:ℝ)
    (hρ:0≤ρ)(hρone:ρ≤1)(hK:0≤K)(hs:0≤s)(hδ:0≤δ)(hv:0≤v)(hC:0≤C)
    (r ri rj di dj:ℕ)(hri:r≤ri+di)(hrj:r≤rj+dj)
    (ha:‖a‖≤K*ρ^di+s)(hb:‖b‖≤K*ρ^dj+s)
    (he:‖e‖≤δ+v*ρ^(ri+rj))(hecap:‖e‖≤C) :
    ‖a*e*b‖≤K^2*δ+K^2*v*ρ^(2*r)+C*s*(2*K+s) := by
  have hi:0≤ρ^di:=pow_nonneg hρ _
  have hj:0≤ρ^dj:=pow_nonneg hρ _
  have hi1:ρ^di≤1:=pow_le_one₀ hρ hρone
  have hj1:ρ^dj≤1:=pow_le_one₀ hρ hρone
  have hp:ρ^(di+dj)*ρ^(ri+rj)≤ρ^(2*r):=by
    rw [←pow_add]
    exact pow_le_pow_of_le_one hρ hρone (by omega)
  have hij:0≤ρ^(di+dj):=pow_nonneg hρ _
  have hij1:ρ^(di+dj)≤1:=pow_le_one₀ hρ hρone
  have hmain:K^2*ρ^(di+dj)*‖e‖≤K^2*δ+K^2*v*ρ^(2*r):=by
    calc
      _≤K^2*ρ^(di+dj)*(δ+v*ρ^(ri+rj)):=mul_le_mul_of_nonneg_left he (by positivity)
      _=K^2*δ*ρ^(di+dj)+K^2*v*(ρ^(di+dj)*ρ^(ri+rj)):=by ring
      _≤K^2*δ*1+K^2*v*ρ^(2*r):=add_le_add
        (mul_le_mul_of_nonneg_left hij1 (by positivity))
        (mul_le_mul_of_nonneg_left hp (by positivity))
      _=_:=by ring
  have hres:s*(K*ρ^di+K*ρ^dj+s)*‖e‖≤C*s*(2*K+s):=by
    have hsum:K*ρ^di+K*ρ^dj+s≤2*K+s:=by
      nlinarith only [mul_le_mul_of_nonneg_left hi1 hK,mul_le_mul_of_nonneg_left hj1 hK]
    have hh:=mul_le_mul (mul_le_mul_of_nonneg_left hsum hs) hecap (norm_nonneg _) (by positivity:0≤s*(2*K+s))
    exact hh.trans_eq (by ring)
  have hnorm:‖a*e*b‖≤(K*ρ^di+s)*‖e‖*(K*ρ^dj+s):=by
    simp only [norm_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_right ha (norm_nonneg _)) hb (norm_nonneg _) (by positivity)
  have heq:(K*ρ^di+s)*‖e‖*(K*ρ^dj+s)=
      K^2*ρ^(di+dj)*‖e‖+s*(K*ρ^di+K*ρ^dj+s)*‖e‖:=by rw [pow_add];ring
  exact hnorm.trans (heq.le.trans (add_le_add hmain hres))

theorem weighted_asymmetric_core_sum {I:Type*} [Fintype I]
    (a b:I→ℂ)(E:Matrix I I ℂ)(ρ K s δ v C:ℝ)
    (hρ:0≤ρ)(hρone:ρ≤1)(hK:0≤K)(hs:0≤s)(hδ:0≤δ)(hv:0≤v)(hC:0≤C)
    (r:ℕ)(ri di dj:I→ℕ)(hri:∀i,r≤ri i+di i)(hrj:∀j,r≤ri j+dj j)
    (ha:∀i,‖a i‖≤K*ρ^(di i)+s)(hb:∀j,‖b j‖≤K*ρ^(dj j)+s)
    (he:∀i j,‖E i j‖≤δ+v*ρ^(ri i+ri j))(hecap:∀i j,‖E i j‖≤C) :
    ‖∑i,∑j,a i*E i j*b j‖≤(Fintype.card I:ℝ)^2*
      (K^2*δ+K^2*v*ρ^(2*r)+C*s*(2*K+s)) := by
  have hp (i j:I):‖a i*E i j*b j‖≤K^2*δ+K^2*v*ρ^(2*r)+C*s*(2*K+s):=
    weighted_asymmetric_core_term (a i) (E i j) (b j) ρ K s δ v C hρ hρone hK hs hδ hv hC
      r (ri i) (ri j) (di i) (dj j) (hri i) (hrj j) (ha i) (hb j) (he i j) (hecap i j)
  calc
    _≤∑i,∑j,‖a i*E i j*b j‖:=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _=>norm_sum_le _ _))
    _≤∑_i:I,∑_j:I,(K^2*δ+K^2*v*ρ^(2*r)+C*s*(2*K+s)):=
      Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>hp i j))
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring

end LocalLaw
