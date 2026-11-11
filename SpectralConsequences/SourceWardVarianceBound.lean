import SpectralConsequences.RefinedWardAlgebra
import SpectralConsequences.SourceRefinedSwitchingChange
import SpectralConsequences.SourceMomentVariance
import SpectralConsequences.SourceResidualChanges
import SpectralConsequences.KestenMcKayImaginaryLower

/-! Both genuine corrected global observable increments are bounded by the
same source Ward variance, with every graph and model input discharged. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceWardVarianceBoundDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceImaginaryCoefficient (d:ℕ):ℝ:=finiteReferenceConstant d+pairSensitivityConstant d+1

def sourceWardVarianceConstant (d:ℕ)(B:ℝ):ℝ:=
  33*((d:ℝ)*((d:ℝ)+1))*refinedWardCoefficient (sourceGreenEntryCap d) (sourceGreenPivotCap d B)
    (2*(B+2)^2) (sourceImaginaryCoefficient d)

theorem sourceWardVarianceConstant_nonnegative (d:ℕ)(B:ℝ)(hd:3≤d)(hB:0≤B):
    0≤sourceWardVarianceConstant d B:=by
  have hC:=finiteReferenceConstant_ge_one d hd
  have hK:=pairSensitivityConstant_nonnegative d
  dsimp only [sourceWardVarianceConstant,refinedWardCoefficient,sourceGreenEntryCap,
    sourceGreenPivotCap,sourceImaginaryCoefficient]
  positivity

namespace RegularGraph

theorem eventually_source_ward_variance_bound (a b d:ℕ)(c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hB:0≤B):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      let new:=g.labelledResampledGraph T labels samples (logarithmicRadius (c/4) d N/4)
      new.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      let V:=sourceMomentVariance a d N (logarithmicRadius β d N) (sourceWardVarianceConstant d B) z
      ‖g.Q z-new.Q z‖≤V ∧
      ‖empiricalTransform g.H z-empiricalTransform new.H z‖≤V ∧
      ‖(g.Q z-cavityIterate z (g.Q z) (ell+1)-trivialCavityCorrection N d ell z)-
        (new.Q z-cavityIterate z (new.Q z) (ell+1)-trivialCavityCorrection N d ell z)‖≤V ∧
      ‖(empiricalTransform g.H z-regularRootValue d ell (g.Q z) z-trivialTraceCorrection N d ell z)-
        (empiricalTransform new.H z-regularRootValue d ell (new.Q z) z-trivialTraceCorrection N d ell z)‖≤V:=by
  filter_upwards [eventually_source_refined_switching_change a b d c β B ha hb hd hc hβ hβc hB,
    eventually_source_residual_changes a b d β ha hb hd hβ,
    eventually_actual_boundary_card_log_bound a d hd (by omega),
    Filter.eventually_ge_atTop 1] with N hraw hres hcount hN
  intro g o z hz hfloor hzB badCount hold ι _ labels samples
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let new:=g.labelledResampledGraph T labels samples (logarithmicRadius (c/4) d N/4)
  let C:=sourceGreenEntryCap d
  let P:=sourceGreenPivotCap d B
  let H:=2*(B+2)^2
  let K:=sourceImaginaryCoefficient d
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let Ψ:=scalarScale (spectralScale z) ε
  let v:=(graphKestenMcKayReference d z).im
  let J:=v+ε+Ψ
  let μ:ℝ:=Nat.card (BoundaryOrientedEdge g.graph T)
  let U:ℝ:=(d:ℝ)*((d:ℝ)+1)
  let A:=refinedWardCoefficient C P H K
  let W:=A*U*Real.log (N:ℝ)^(2*a)*J/((N:ℝ)*z.im)
  let V:=sourceMomentVariance a d N (logarithmicRadius β d N) (sourceWardVarianceConstant d B) z
  intro hnew
  have hC:0≤C:=by have hh:=finiteReferenceConstant_ge_one d hd;dsimp only [C,sourceGreenEntryCap];linarith
  have hP:0≤P:=by have hh:=finiteReferenceConstant_ge_one d hd;dsimp only [P,sourceGreenPivotCap];positivity
  have hK:0≤K:=by
    have hh:=finiteReferenceConstant_ge_one d hd
    have hh':=pairSensitivityConstant_nonnegative d
    dsimp only [K,sourceImaginaryCoefficient];positivity
  have hε:0≤ε:=graphPaperError_nonnegative _ _ _ _ _ hN hz.le
  have hΨ:0≤Ψ:=scalarScale_nonneg hε
  have hv:0≤v:=(kestenMcKayTransform_im_pos d (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le).le
  have hI:0≤sourceRefinedImaginaryCap (N:=N) a d (logarithmicRadius β d N) z:=by
    have hh:=finiteReferenceConstant_ge_one d hd
    have hh':=pairSensitivityConstant_nonnegative d
    dsimp only [sourceRefinedImaginaryCap]
    positivity
  have hIJ:sourceRefinedImaginaryCap (N:=N) a d (logarithmicRadius β d N) z≤K*J:=by
    have hCc:0≤finiteReferenceConstant d:=(by norm_num:(0:ℝ)≤1).trans (finiteReferenceConstant_ge_one d hd)
    have hpair:=pairSensitivityConstant_nonnegative d
    dsimp only [sourceRefinedImaginaryCap,K,J,v,ε,Ψ,sourceImaginaryCoefficient]
    nlinarith [mul_nonneg hCc hε,mul_nonneg hCc hΨ,
      mul_nonneg hpair hv,mul_nonneg hpair hε]
  have hheight:z.im≤H*J:=by
    have hh:=bounded_height_le_reference_imaginary d hd z hz B hzB
    change z.im≤H*v at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (show 0≤H by dsimp only [H];positivity)
    change v≤v+ε+Ψ
    linarith
  have halgebra:=refined_ward_budgets N d μ C P H K _ J z.im (by omega) hd (Nat.cast_nonneg _)
    hC hP (by dsimp only [H];positivity) hK hI (by dsimp only [J];positivity) hz hheight hIJ
  have hraw':=hraw g o z hz hfloor hzB badCount hold labels samples hnew
  have hμ:μ≤U*Real.log (N:ℝ)^(2*a):=hcount g o z
  have hA:0≤A:=by dsimp only [A,refinedWardCoefficient];positivity
  have hW:0≤W:=by dsimp only [W,J,U];positivity
  have hbudget:A*μ*J/((N:ℝ)*z.im)≤W:=by
    have hh:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hμ hA) (show 0≤J by dsimp only [J];positivity)) (by positivity:(0:ℝ)≤(N:ℝ)*z.im)
    convert hh using 1;ring
  have hQ:‖g.Q z-new.Q z‖≤W:=hraw'.1.trans (halgebra.1.trans hbudget)
  have htrace:‖empiricalTransform g.H z-empiricalTransform new.H z‖≤W:=hraw'.2.trans (halgebra.2.trans hbudget)
  have hV:V=33*W:=by dsimp only [V,W,sourceMomentVariance,sourceWardVarianceConstant,A,U,C,P,H,K,J,v,ε,Ψ];ring
  have hWV:W≤V:=by rw [hV];nlinarith
  have hres':=hres g new z hz hfloor (logarithmicRadius (c/4) d N) (finiteOmega d) badCount badCount hold hnew
  refine ⟨hQ.trans hWV,htrace.trans hWV,?_,?_⟩
  · exact hres'.1.trans ((mul_le_mul_of_nonneg_left hQ (by norm_num:(0:ℝ)≤5)).trans (by change 5*W≤V;rw [hV];nlinarith))
  · exact hres'.2.trans ((add_le_add htrace (mul_le_mul_of_nonneg_left hQ (by norm_num:(0:ℝ)≤32))).trans (by change W+32*W≤V;rw [hV];nlinarith))

/-- The fixed actual Ward variance is smaller than the source increment,
without a spectral-event or a variance-smallness hypothesis. -/
theorem eventually_source_ward_variance_small (a b d:ℕ)(β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hβ:0<β)(hB:0≤B):
    ∀ᶠ N:ℕ in Filter.atTop,∀z:ℂ,0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      let V:=sourceMomentVariance a d N (logarithmicRadius β d N) (sourceWardVarianceConstant d B) z
      0≤V ∧ V≤ε/Real.log (N:ℝ)^16 ∧ V≤ε:=by
  filter_upwards [eventually_source_moment_variance_small a b d β (sourceWardVarianceConstant d B)
    ha hb hd hβ (sourceWardVarianceConstant_nonnegative d B hd hB)] with N hN
  intro z hz hfloor
  exact (hN z hz hfloor).1

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_source_ward_variance_bound
