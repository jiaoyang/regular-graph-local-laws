import SpectralConsequences.TrivialCorrectionEstimate
import LocalLaw.ClosureParameters

/-! Source-(7.40) in its spectral scale, at the actual nonresonant depth. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem cavity_power_gap_nonresonant (z:ℂ)(hz:0<z.im)(B:ℝ)(hB:‖z‖≤B)
    (n:ℕ)(hn:1/2≤‖cavitySum (semicircleRoot z) n‖):
    Real.sqrt (spectralScale z)/(2*(B+1))≤‖1-(semicircleRoot z)^(2*n)‖:=by
  let m:=semicircleRoot z
  have hB0:0≤B:=(norm_nonneg z).trans hB
  have hBp:0<B+1:=by linarith
  have hm0:m≠0:=semicircleRoot_ne_zero z
  have hfactor:1-m^2=m*(m⁻¹-m):=by rw [mul_sub,mul_inv_cancel₀ hm0];ring
  have hgeom:=cavitySum_geometric m n
  rw [hfactor] at hgeom
  have hnorm:=congrArg norm hgeom
  simp only [norm_mul] at hnorm
  have hlower:=mul_le_mul (mul_le_mul (cavity_root_norm_lower_bound (semicircleRoot_equation z)
    (semicircleRoot_norm_le_one z) hB) (cavity_root_gap_bounds (semicircleRoot_equation z) hz hB).1
      (Real.sqrt_nonneg _) (norm_nonneg m)) hn (by norm_num) (by positivity)
  rw [hnorm] at hlower
  calc
    _=(1/(B+1))*Real.sqrt (spectralScale z)*(1/2):=by rw [mul_comm (2:ℝ) (B+1),div_mul_eq_div_div];ring
    _≤_:=hlower

def trivialCancellationSpectralConstant (d:ℕ)(B:ℝ):ℝ:=
  trivialCancellationConstant d*(2*(B+1))

theorem trivial_correction_cancellation_spectral (N d ell:ℕ)(hN:1≤N)(hd:3≤d)
    (z:ℂ)(hz:0<z.im)(B:ℝ)(hB:‖z‖≤B)
    (hn:1/2≤‖cavitySum (semicircleRoot z) (ell+1)‖):
    ‖trivialTraceCorrection N d ell z+
      regularRootLinearCoefficient d ell (semicircleRoot z) (kestenMcKayTransform d (semicircleRoot z) z)/
        (1-(semicircleRoot z)^(2*ell+2))*trivialCavityCorrection N d ell z-trivialPole N d z‖≤
      trivialCancellationSpectralConstant d B*(ell+1)*((d-1:ℕ):ℝ)^ell/
        ((N:ℝ)*Real.sqrt (spectralScale z)):=by
  have hB0:0≤B:=(norm_nonneg z).trans hB
  have hNp:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  have hs:0<Real.sqrt (spectralScale z):=Real.sqrt_pos.mpr (spectralScale_pos hz)
  have hgap:=cavity_power_gap_nonresonant z hz B hB (ell+1) hn
  rw [show 2*(ell+1)=2*ell+2 by omega] at hgap
  have hT:1-(semicircleRoot z)^(2*ell+2)≠0:=norm_pos_iff.mp
    (lt_of_lt_of_le (by positivity:0<Real.sqrt (spectralScale z)/(2*(B+1))) hgap)
  apply (trivial_correction_cancellation_bound N d ell hN hd z hz hT).trans
  have hden:((N:ℝ)*(Real.sqrt (spectralScale z)/(2*(B+1))))≤
      ((N:ℝ)*‖1-(semicircleRoot z)^(2*ell+2)‖):=
    mul_le_mul_of_nonneg_left hgap hNp.le
  apply (div_le_div_of_nonneg_left (by unfold trivialCancellationConstant;positivity)
    (by positivity) hden).trans_eq
  unfold trivialCancellationSpectralConstant
  field_simp
  ring

/-- The source chooses its depth from two adjacent actual log-log radii. Thus
its nonresonance premise is a theorem, uniformly in z and N. -/
theorem actual_depth_trivial_correction_cancellation (a N d:ℕ)(hN:1≤N)(hd:3≤d)
    (z:ℂ)(hz:0<z.im)(B:ℝ)(hB:‖z‖≤B):
    let ell:=actualCavityDepth a d N z-1
    ‖trivialTraceCorrection N d ell z+
      regularRootLinearCoefficient d ell (semicircleRoot z) (kestenMcKayTransform d (semicircleRoot z) z)/
        (1-(semicircleRoot z)^(2*ell+2))*trivialCavityCorrection N d ell z-trivialPole N d z‖≤
      trivialCancellationSpectralConstant d B*(ell+1)*((d-1:ℕ):ℝ)^ell/
        ((N:ℝ)*Real.sqrt (spectralScale z)):=by
  dsimp only
  apply trivial_correction_cancellation_spectral N d _ hN hd z hz B hB
  have hb:2≤baselineCavityDepth a d N:=by unfold baselineCavityDepth;omega
  have hh:baselineCavityDepth a d N≤actualCavityDepth a d N z:=
    (nonresonantDepth_bounds (semicircleRoot z) (baselineCavityDepth a d N)).1
  have hn:actualCavityDepth a d N z-1+1=actualCavityDepth a d N z:=by omega
  rw [hn]
  exact nonresonantDepth_valid _ _ (semicircleRoot_norm_le_one z)

end SpectralConsequences
#print axioms SpectralConsequences.actual_depth_trivial_correction_cancellation
