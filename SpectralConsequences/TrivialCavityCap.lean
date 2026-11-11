import SpectralConsequences.TrivialPoleCancellation

/-! A literal global cap on the cavity correction, including at the known pole. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem trivialPole_norm_le (N d:ℕ)(hN:1≤N)(z:ℂ)(hz:0<z.im):
    ‖trivialPole N d z‖≤1/((N:ℝ)*z.im):=by
  let w:=(d:ℂ)*treeEdgeWeight d-z
  have hw:z.im≤‖w‖:=by
    simpa only [w,treeEdgeWeight,Complex.sub_im,Complex.mul_im,Complex.natCast_im,
      Complex.ofReal_im,zero_mul,mul_zero,add_zero,zero_sub,abs_neg,abs_of_pos hz] using
      Complex.abs_im_le_norm w
  have hNp:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  simp only [trivialPole,norm_mul,norm_inv,Complex.norm_natCast]
  change (N:ℝ)⁻¹*‖w‖⁻¹≤1/((N:ℝ)*z.im)
  calc
    _≤(N:ℝ)⁻¹*z.im⁻¹:=mul_le_mul_of_nonneg_left
      (by simpa only [one_div] using one_div_le_one_div_of_le hz hw) (by positivity)
    _=_:=by field_simp

theorem cavityCorrectionCoefficient_norm_le (d ell:ℕ)(hd:3≤d)(z:ℂ):
    ‖cavityCorrectionCoefficient d ell (semicircleRoot z)‖≤
      8*((d-1:ℕ):ℝ)^(ell+1):=by
  let m:=semicircleRoot z
  let K:=((d-1:ℕ):ℝ)^(ell+1)
  have hK:1≤K:=one_le_pow₀ (by exact_mod_cast (show 1≤d-1 by omega))
  have hm:‖m‖≤1:=semicircleRoot_norm_le_one z
  have hα:‖treeEdgeWeight d‖≤1:=(treeEdgeWeight_norm_le_three_quarters d hd).trans (by norm_num)
  have hfactor:‖1+m*treeEdgeWeight d‖≤2:=by
    apply (norm_add_le _ _).trans
    simp only [norm_one,norm_mul]
    have hh:=mul_le_mul hm hα (norm_nonneg _) (by norm_num)
    linarith
  have hfirst:‖(((d-1:ℕ):ℂ)^(ell+1))-1‖≤2*K:=by
    have hh:=norm_sub_le ((((d-1:ℕ):ℂ)^(ell+1))) (1:ℂ)
    simp only [norm_pow,Complex.norm_natCast,norm_one] at hh
    dsimp only [K] at hK ⊢
    linarith
  unfold cavityCorrectionCoefficient
  change ‖(((((d-1:ℕ):ℂ)^(ell+1))-1)*m^(2*ell+2))*(1+m*treeEdgeWeight d)^2‖≤8*K
  simp only [norm_mul,norm_pow]
  have hpow:‖m‖^(2*ell+2)≤1:=pow_le_one₀ (norm_nonneg _) hm
  have hs:‖1+m*treeEdgeWeight d‖^2≤4:=by nlinarith [norm_nonneg (1+m*treeEdgeWeight d)]
  have hh:=mul_le_mul (mul_le_mul hfirst hpow (by positivity) (by positivity)) hs (by positivity) (by positivity)
  exact hh.trans_eq (by ring)

theorem trivialCavityCorrection_norm_le (N d ell:ℕ)(hN:1≤N)(hd:3≤d)(z:ℂ)(hz:0<z.im):
    ‖trivialCavityCorrection N d ell z‖≤
      8*((d-1:ℕ):ℝ)^(ell+1)/((N:ℝ)*z.im):=by
  unfold trivialCavityCorrection
  rw [norm_mul]
  have hh:=mul_le_mul (cavityCorrectionCoefficient_norm_le d ell hd z)
    (trivialPole_norm_le N d hN z hz) (norm_nonneg _) (by positivity)
  exact hh.trans_eq (by ring)

end SpectralConsequences
#print axioms SpectralConsequences.trivialCavityCorrection_norm_le
