import LocalLaw.SwitchingQParameters
import LocalLaw.BoundaryPerturbationParameters
import LocalLaw.ScalarStability

/-! The refined Ward variance remains genuine, while its comparison with
the local source increment follows from the actual fractional error floor. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw

def sourceMomentVariance (a d N r:ℕ)(K:ℝ)(z:ℂ):ℝ:=
  K*Real.log (N:ℝ)^(2*a)*((graphKestenMcKayReference d z).im+graphPaperError a d N r z+
    scalarScale (spectralScale z) (graphPaperError a d N r z))/((N:ℝ)*z.im)

def sourcePrimeMomentVariance (a d N r:ℕ)(K:ℝ)(z:ℂ):ℝ:=
  K*Real.log (N:ℝ)^(2*a)*((graphKestenMcKayReference d z).im+
    inflatedPrime (Real.log (N:ℝ)) (graphPaperError a d N r z)+
    scalarScale (spectralScale z) (graphPaperError a d N r z))/((N:ℝ)*z.im)

theorem eventually_source_moment_variance_small (a b d:ℕ)(β K:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hβ:0<β)(hK:0≤K):
    ∀ᶠ N:ℕ in Filter.atTop,∀z:ℂ,0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      let r:=logarithmicRadius β d N
      let ε:=graphPaperError a d N r z
      (0≤sourceMomentVariance a d N r K z ∧
        sourceMomentVariance a d N r K z≤ε/Real.log (N:ℝ)^16 ∧
        sourceMomentVariance a d N r K z≤ε) ∧
      (0≤sourcePrimeMomentVariance a d N r K z ∧
        sourcePrimeMomentVariance a d N r K z≤ε/Real.log (N:ℝ)^16 ∧
        sourcePrimeMomentVariance a d N r K z≤ε):=by
  filter_upwards [eventually_switching_change_absorption a b d (4*K) 1 ha hb (by positivity) (by norm_num),
    eventually_paperError_small a b d β ha hb hd hβ,eventually_log_ge_nat 1,
    Filter.eventually_ge_atTop 1] with N habs hsmall hlog hN
  intro z hz hfloor
  dsimp only
  let r:=logarithmicRadius β d N
  let ε:=graphPaperError a d N r z
  let L:=Real.log (N:ℝ)
  let Ψ:=scalarScale (spectralScale z) ε
  let v:=(graphKestenMcKayReference d z).im
  have hn:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  have hL:0<L:=by dsimp only [L];linarith
  have hε:0≤ε:=graphPaperError_nonnegative _ _ _ _ _ hN hz.le
  have he:ε≤1:=by
    have hh:=hsmall z hz hfloor
    exact hh.trans ((inv_le_one₀ (pow_pos hL _)).mpr (one_le_pow₀ hlog))
  have hecap:ε*L^(4*a)≤1:=(le_div_iff₀ (pow_pos hL _)).mp (by simpa only [one_div] using hsmall z hz hfloor)
  have heprime:0≤L^3*ε ∧ L^3*ε≤1:=by
    constructor
    · positivity
    · have hh:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hlog (show 3≤4*a by omega)) hε
      exact hh.trans (by simpa only [mul_comm ε] using hecap)
  have hΨ:0≤Ψ:=scalarScale_nonneg hε
  have hΨ1:Ψ≤1:=(scalarScale_le_sqrt (spectralScale_pos hz) hε).trans
    (Real.sqrt_le_one.mpr he)
  have hv:0≤v:=(kestenMcKayTransform_im_pos d (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le).le
  have hv2:v≤2:=((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (kestenMcKayTransform_norm_le_two d hd z hz)
  have happly (I:ℝ)(hI0:0≤I)(hI:I≤4):
      0≤K*L^(2*a)*I/((N:ℝ)*z.im) ∧
      K*L^(2*a)*I/((N:ℝ)*z.im)≤ε/L^16 ∧
      K*L^(2*a)*I/((N:ℝ)*z.im)≤ε:=by
    have hδ:K*L^(2*a)*I/((N:ℝ)*z.im)≤(4*K)*L^(2*a)/((N:ℝ)*z.im):=by
      have hh:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hI
        (show 0≤K*L^(2*a) by positivity)) (mul_nonneg hn.le hz.le)
      convert hh using 1;ring
    have hh:=habs z r (L^(2*a)) (K*L^(2*a)*I/((N:ℝ)*z.im)) hz hfloor (by simp only [L,one_mul,le_refl]) hδ
    exact ⟨by positivity,hh,hh.trans (div_le_self hε (one_le_pow₀ hlog))⟩
  exact ⟨happly (v+ε+Ψ) (by positivity) (by linarith),
    happly (v+L^3*ε+Ψ) (by positivity) (by linarith [heprime.2])⟩

end SpectralConsequences
#print axioms SpectralConsequences.eventually_source_moment_variance_small
