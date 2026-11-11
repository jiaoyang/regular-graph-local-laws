import SpectralConsequences.CorrectedTraceStability
import SpectralConsequences.TrivialCavityCap
import SpectralConsequences.SourceCorrectedTrace
import LocalLaw.SourceLocalLawIdentifiers

/-! # Actual graph trace correction at its genuine selected cavity depth

The two fluctuation residuals are explicit physical quantities. Depth
nonresonance, the physical Q half-plane condition, the cavity correction cap,
and the exact removed eigenvalue pole are all derived.
-/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceCorrectedResidualsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceCorrectedGap (z:ℂ) (B:ℝ):ℝ:=Real.sqrt (spectralScale z)/(2*(B+1))
def sourceTrivialCorrectionCap (a d N:ℕ) (z:ℂ):ℝ:=
  8*((d-1:ℕ):ℝ)^((actualCavityDepth a d N z-1)+1)/((N:ℝ)*z.im)

def physicalCavityFluctuation {N d:ℕ} (a:ℕ) (g:RegularGraph N d) (z:ℂ):ℂ:=
  g.Q z-cavityIterate z (g.Q z) (actualCavityDepth a d N z)-
    trivialCavityCorrection N d (actualCavityDepth a d N z-1) z

def physicalTraceFluctuation {N d:ℕ} (a:ℕ) (g:RegularGraph N d) (z:ℂ):ℂ:=
  empiricalTransform g.H z-regularRootValue d (actualCavityDepth a d N z-1) (g.Q z) z-
    trivialTraceCorrection N d (actualCavityDepth a d N z-1) z

theorem realSourcePaperError_nat_eq_graph (a d N r:ℕ) (hd:3≤d) (z:ℂ) (hz:0<z.im):
    realSourcePaperError (a:ℝ) d N r z=graphPaperError a d N r z:=by
  rw [realSourcePaperError_eq_graph (a:ℝ) d N r hd z hz]
  unfold realGraphPaperError graphPaperError paperError paperBaseError baseError
  congr 1
  norm_cast

theorem correctedSourceTrace_sub_reference {N d:ℕ} (g:RegularGraph N d) (z:ℂ):
    RegularGraph.correctedSourceTrace g z-kestenMcKayStieltjes d z=
      empiricalTransform g.H z-kestenMcKayStieltjes d z-trivialPole N d z := by
  unfold RegularGraph.correctedSourceTrace trivialPole regularSpectralRadius treeEdgeWeight
  simp only[Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_inv,div_eq_mul_inv,Complex.ofReal_mul]
  ring

namespace RegularGraph

theorem actual_corrected_trace_bound_of_residuals {N d:ℕ} (g:LocalLaw.RegularGraph N d)
    (a:ℕ) (hN:1≤N) (hd:3≤d) (z:ℂ) (hz:0<z.im) (B:ℝ) (hB:‖z‖≤B)
    (Rc Rt u:ℝ) (hprior:‖g.Q z-semicircleRoot z‖≤u)
    (hpriorSmall:(((actualCavityDepth a d N z-1:ℕ):ℝ)+4)*u≤1/2)
    (hsmall:(((actualCavityDepth a d N z-1:ℕ):ℝ)+1)*
      (u+sourceTrivialCorrectionCap a d N z*(1/sourceCorrectedGap z B+1))≤sourceCorrectedGap z B/2)
    (hresQ:‖physicalCavityFluctuation a g z‖≤Rc)
    (hresTrace:‖physicalTraceFluctuation a g z‖≤Rt):
    let ell:=actualCavityDepth a d N z-1
    let C0:=sourceTrivialCorrectionCap a d N z
    let gap:=sourceCorrectedGap z B
    ‖RegularGraph.correctedSourceTrace g z-kestenMcKayStieltjes d z‖≤
      Rt+16*((ell:ℝ)+4)*u^2+24*Rc/gap+48*((ell:ℝ)+1)*C0^2/gap^3+
        trivialCancellationSpectralConstant d B*(ell+1)*((d-1:ℕ):ℝ)^ell/
          ((N:ℝ)*Real.sqrt (spectralScale z)) := by
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  have hb:2≤baselineCavityDepth a d N:=by unfold baselineCavityDepth;omega
  have hdepth:baselineCavityDepth a d N≤actualCavityDepth a d N z:=
    (nonresonantDepth_bounds (semicircleRoot z) (baselineCavityDepth a d N)).1
  have hell:ell+1=actualCavityDepth a d N z:=by dsimp only[ell];omega
  have hn:1/2≤‖cavitySum (semicircleRoot z) (ell+1)‖:=by
    rw [hell]
    exact nonresonantDepth_valid _ _ (semicircleRoot_norm_le_one z)
  have hB0:0≤B:=(norm_nonneg z).trans hB
  have hgap:0<sourceCorrectedGap z B:=by
    unfold sourceCorrectedGap
    exact div_pos (Real.sqrt_pos.mpr (spectralScale_pos hz)) (by positivity)
  have hpow:sourceCorrectedGap z B≤‖1-(semicircleRoot z)^(2*ell+2)‖:=by
    simpa only[Nat.mul_add,Nat.mul_one,sourceCorrectedGap] using
      cavity_power_gap_nonresonant z hz B hB (ell+1) hn
  have hc:‖trivialCavityCorrection N d ell z‖≤sourceTrivialCorrectionCap a d N z:=
    trivialCavityCorrection_norm_le N d ell hN hd z hz
  have hq:‖g.Q z-cavityIterate z (g.Q z) (ell+1)-trivialCavityCorrection N d ell z‖≤Rc:=by
    simpa only[hell,ell,physicalCavityFluctuation] using hresQ
  have ht:‖empiricalTransform g.H z-regularRootValue d ell (g.Q z) z-trivialTraceCorrection N d ell z‖≤Rt:=hresTrace
  have hh:=corrected_trace_bound_of_residuals N d ell hN hd z (g.Q z) (empiricalTransform g.H z) hz
    (g.Q_im_nonnegative z hz) B hB hn Rc Rt u (sourceTrivialCorrectionCap a d N z)
    (sourceCorrectedGap z B) hgap hpow hprior hc hpriorSmall hsmall hq ht
  rw [←correctedSourceTrace_sub_reference g z] at hh
  exact hh

end RegularGraph
end SpectralConsequences
