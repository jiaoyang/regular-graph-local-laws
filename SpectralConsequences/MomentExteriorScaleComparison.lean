import SpectralConsequences.SourceMomentVariance
import SpectralConsequences.SourceExteriorResidualBound

/-! The high-moment scale retains its Ward factor and is bounded by a fixed
logarithmic multiple of the actual exterior fluctuation scale. -/
noncomputable section
set_option maxHeartbeats 1400000
namespace SpectralConsequences
open LocalLaw

theorem source_moment_scale_le_exterior (a d N:ℕ)(β γ K:ℝ)(hd:3≤d)(hN:1≤N)
    (hL:1≤Real.log (N:ℝ))(hK:0≤K)(z:ℂ)(hz:0<z.im):
    let ε:=graphPaperError a d N (logarithmicRadius β d N) z
    ε^2+Real.sqrt (ε*sourceMomentVariance a d N (logarithmicRadius β d N) K z)≤
      (K+1)*Real.log (N:ℝ)^(2*a)*sourceExteriorFluctuationScale a d N β γ z:=by
  dsimp only
  let L:=Real.log (N:ℝ)
  let ell:=actualCavityDepth a d N z-1
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let εp:=inflatedPrime L ε
  let Ψ:=scalarScale (spectralScale z) ε
  let kpow:=((d-1:ℕ):ℝ)^(2*ell)
  let I:ℝ:=(kestenMcKayStieltjes d z).im+εp+Ψ
  let D:ℝ:=kpow*I/((N:ℝ)*z.im)
  let H:ℝ:=(K+1)*L^(2*a)
  have hLp:0≤L:=by dsimp only [L];linarith
  have hLp2:1≤L^(2*a):=one_le_pow₀ hL
  have hε:0≤ε:=graphPaperError_nonnegative _ _ _ _ _ hN hz.le
  have hΨ:0≤Ψ:=scalarScale_nonneg hε
  have hεp:0≤εp:=by change 0≤L^3*ε;positivity
  have heprime:ε≤εp:=by
    change ε≤L^3*ε
    exact le_mul_of_one_le_left hε (one_le_pow₀ hL)
  have hm:0≤(kestenMcKayStieltjes d z).im:=by
    rw [kestenMcKayStieltjes_eq_transform d hd z hz]
    exact (kestenMcKayTransform_im_pos d (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le).le
  have hI:0≤I:=by dsimp only [I];positivity
  have hk:1≤kpow:=one_le_pow₀ (by exact_mod_cast (show 1≤d-1 by omega))
  have hD:0≤D:=by dsimp only [D];positivity
  have hH:1≤H:=by dsimp only [H];nlinarith
  have hHref:0≤H:=by linarith
  have href:(graphKestenMcKayReference d z).im=(kestenMcKayStieltjes d z).im:=by
    rw [kestenMcKayStieltjes_eq_transform d hd z hz]
    rfl
  have hv:sourceMomentVariance a d N (logarithmicRadius β d N) K z≤K*L^(2*a)*D:=by
    unfold sourceMomentVariance
    rw [href]
    change K*L^(2*a)*((kestenMcKayStieltjes d z).im+ε+Ψ)/((N:ℝ)*z.im)≤K*L^(2*a)*D
    dsimp only [D]
    rw [←mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (add_le_add_right (add_le_add_left heprime _) _).trans (le_mul_of_one_le_left hI hk)
  have hfactor:Real.sqrt (K*L^(2*a))≤H:=by
    have hS:0≤K*L^(2*a):=by positivity
    have hb:K*L^(2*a)+1≤H:=by dsimp only [H];nlinarith
    have hs:(K*L^(2*a)+1)^2≤H^2:=sq_le_sq₀ (by positivity) hHref |>.mpr hb
    apply Real.sqrt_le_iff.mpr
    exact ⟨hHref,by nlinarith [sq_nonneg (K*L^(2*a))]⟩
  have hward:Real.sqrt (ε*sourceMomentVariance a d N (logarithmicRadius β d N) K z)≤
      H*(Real.sqrt ε*Real.sqrt D):=by
    apply (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hv hε)).trans
    rw [show ε*(K*L^(2*a)*D)=(K*L^(2*a))*(ε*D) by ring,
      Real.sqrt_mul (by positivity:0≤K*L^(2*a)),Real.sqrt_mul hε]
    exact mul_le_mul_of_nonneg_right hfactor (by positivity)
  have hquad:ε^2≤H*(kpow*εp^2):=by
    have hsq:ε^2≤εp^2:=sq_le_sq₀ hε hεp |>.mpr heprime
    exact (hsq.trans (le_mul_of_one_le_left (sq_nonneg εp) hk)).trans
      (le_mul_of_one_le_left (by positivity) hH)
  change ε^2+Real.sqrt (ε*sourceMomentVariance a d N (logarithmicRadius β d N) K z)≤
    H*(Real.sqrt ε*Real.sqrt D+kpow*εp^2+εp/(N:ℝ)^γ)
  have hextra:0≤εp/(N:ℝ)^γ:=by positivity
  have hh:=add_le_add hquad hward
  nlinarith [mul_nonneg hHref hextra]

end SpectralConsequences
