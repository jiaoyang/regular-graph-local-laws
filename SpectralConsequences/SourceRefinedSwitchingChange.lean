import SpectralConsequences.SourceRefinedImaginary
import LocalLaw.SwitchingQLocalParameters
import LocalLaw.SourceResamplingStructural
import LocalLaw.AdmissibleGreenBlock

/-! Actual refined (7.30) changes of Q and the empirical transform.
Both source memberships derive every entry, pivot and imaginary-part cap. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceRefinedSwitchingChangeDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_refined_switching_change (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hB:0≤B):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let new:=g.labelledResampledGraph T labels samples (logarithmicRadius (c/4) d N/4)
      new.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      let C:=sourceGreenEntryCap d
      let P:=sourceGreenPivotCap d B
      let I:=sourceRefinedImaginaryCap (N:=N) a d (logarithmicRadius β d N) z
      let μ:ℝ:=Nat.card (BoundaryOrientedEdge g.graph T)
      ‖g.Q z-new.Q z‖≤((N:ℝ)*(d:ℝ))⁻¹*
        (((d:ℝ)*(1+C*P)^2*I/z.im)*(8*μ/Real.sqrt ((d:ℝ)-1))+8*μ*(C+C^2*P)) ∧
      ‖empiricalTransform g.H z-empiricalTransform new.H z‖≤
        (N:ℝ)⁻¹*(I/z.im)*(8*μ/Real.sqrt ((d:ℝ)-1)):=by
  have hC:0≤sourceGreenEntryCap d:=by
    have hh:=finiteReferenceConstant_ge_one d hd
    dsimp only [sourceGreenEntryCap];linarith
  have hP:0≤sourceGreenPivotCap d B:=by
    have hh:=finiteReferenceConstant_ge_one d hd
    dsimp only [sourceGreenPivotCap];positivity
  filter_upwards [eventually_source_refined_imaginary a b d c β ha hb hd hc hβ hβc,
    LocalLaw.RegularGraph.eventually_sourceOmegaWithRadii_green_caps a b d c β B ha hb hd hc hβ hβc hB,
    Filter.eventually_ge_atTop 1] with N hIm hcap hN
  intro g o z hz hfloor hzB badCount hold ι _ labels samples
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let s:=g.admissibleState T labels samples
  let new:=g.labelledResampledGraph T labels samples selector
  let C:=sourceGreenEntryCap d
  let P:=sourceGreenPivotCap d B
  let I:=sourceRefinedImaginaryCap (N:=N) a d (logarithmicRadius β d N) z
  let μ:ℝ:=Nat.card (BoundaryOrientedEdge g.graph T)
  intro hnew
  have oldCaps:=hcap g z badCount hz hzB hfloor hold
  have newCaps:=hcap new z badCount hz hzB hfloor hnew
  have oldIm:=hIm g z badCount hz hfloor hold
  have newIm:=hIm new z badCount hz hfloor hnew
  have hε:0≤graphPaperError a d N (logarithmicRadius β d N) z:=
    graphPaperError_nonnegative _ _ _ _ _ hN hz.le
  have hI:0≤I:=by
    have hc':0≤finiteReferenceConstant d:=(by norm_num:(0:ℝ)≤1).trans (finiteReferenceConstant_ge_one d hd)
    have hm:0≤(graphKestenMcKayReference d z).im:=
      (kestenMcKayTransform_im_pos d (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le).le
    have hK:=pairSensitivityConstant_nonnegative d
    have hΨ:=scalarScale_nonneg (s:=spectralScale z) hε
    dsimp only [I,sourceRefinedImaginaryCap]
    positivity
  constructor
  · have hh:=s.fullResample_cavityAverage_difference_local selector d g.regular z hz C P I hC hP hI
      (fun i=>oldCaps.1 i i) (fun i j _=>oldCaps.1 i j) newCaps.1 oldCaps.2 newCaps.2 oldIm newIm
    simpa only [Fintype.card_fin] using hh
  · have hw:=diagonal_green_difference_ward g.H new.H g.H_hermitian new.H_hermitian z hz I oldIm newIm
    have hmass:=s.fullResample_normalized_difference_mass_le selector d
    have hnorm:‖empiricalTransform g.H z-empiricalTransform new.H z‖≤
        (N:ℝ)⁻¹*(∑i,‖g.G z i i-new.G z i i‖):=by
      unfold empiricalTransform
      rw [←mul_sub,norm_mul]
      simp only [Fintype.card_fin,norm_inv,Complex.norm_natCast,Matrix.trace]
      rw [←Finset.sum_sub_distrib]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg N))
    apply hnorm.trans
    calc
      _≤(N:ℝ)⁻¹*((I/z.im)*(∑u,∑v,‖(new.H-g.H) u v‖)):=
        mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr (Nat.cast_nonneg N))
      _≤(N:ℝ)⁻¹*((I/z.im)*(8*μ/Real.sqrt ((d:ℝ)-1))):=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass (div_nonneg hI hz.le))
          (inv_nonneg.mpr (Nat.cast_nonneg N))
      _=_:=by ring

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_source_refined_switching_change
