import SpectralConsequences.SourceCavityLabelledDrift
import SpectralConsequences.SourceBoundaryCorrectionSensitivity

/-! The actual conditional cavity drift with the physical trivial correction. -/
open scoped BigOperators
open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceCavityPhysicalDriftDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ} {T:Set (Fin N)} {ι:Type} [Fintype ι]

def sourceCavityDriftError (g:LocalLaw.RegularGraph N d) (a:ℕ) (β B:ℝ)
    (labels:ι≃BoundaryOrientedEdge g.graph T) (selector r _ell:ℕ) (z:ℂ):ℝ:=
  sourceConditionalCellError g a β B labels selector r z*
      (2*finiteExtraReferenceConstant d*(Nat.card (BoundaryOrientedEdge g.graph T):ℝ))^2+
    cavityRootQuadraticConstant d β (sourceMinorEnlargementConstant d β B)*
      Real.log (N:ℝ)^(6*a+7)*(graphPaperError a d N r z)^2+
    boundaryCorrectionSensitivityConstant d β*Real.log (N:ℝ)^(4*a+1)*
      scalarScale (spectralScale z) (graphPaperError a d N r z)*‖trivialPole N d z‖

theorem eventually_source_cavity_physical_drift (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32) (hB:0≤B):
    ∀ᶠ N:ℕ in atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree→
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      let selector:=logarithmicRadius (c/4) d N/4
      ∃_hell:2≤ell,∀(j:T)(hjo:g.graph.Adj j.val o),
      ∀{ι:Type}[Fintype ι](labels:ι≃BoundaryOrientedEdge g.graph T),
      ‖finiteComplexMean (fun samples:LocalSamplingFiber g.graph T=>
        let new:=g.labelledResampledGraph T labels samples selector
        new.retainedPhysicalMinor T j z (g.truncatedCavityRoot o ell j hjo)
          (g.truncatedCavityRoot o ell j hjo))-
        cavityIterate z (g.Q z) (ell+1)-trivialCavityCorrection N d ell z‖≤
        sourceCavityDriftError g a β B labels selector (logarithmicRadius β d N) ell z:=by
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_source_cavity_labelled_drift a b d c β B ha hb hd hc hβ hβc hB,
    eventually_source_boundary_correction_sensitivity a b d c β B ha hb hd hc hβ hβc,
    eventually_source_truncated_parameter_bounds a b d c β B ha hb hd hc hβ hβc,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,hdepth]
    with N hdrift hcorrection hparam hmargin hdepthN
  intro g o z hz hfloor hzB badCount hold htree
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let q:=g.Q z
  let selector:=logarithmicRadius (c/4) d N/4
  obtain ⟨hell,hdrift'⟩:=hdrift g o z hz hfloor hzB badCount hold htree
  obtain ⟨hell',hcorrection'⟩:=(hcorrection g o z hz hfloor hzB badCount hold htree).2
  refine ⟨hell,?_⟩
  intro j hjo ι _ labels
  let w:ι→ℂ:=fun i=>cavityBoundaryWeight g o ell hell j hjo q z (labels i)
  let e:=sourceConditionalCellError g a β B labels selector (logarithmicRadius β d N) z
  let μ:ℝ:=Nat.card (BoundaryOrientedEdge g.graph T)
  have hC:0≤finiteExtraReferenceConstant d:=(by norm_num:(0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hellBound:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepthN).2
  have htreeEll:=(graphBall_tree_mono g.graph o (show ell≤logarithmicRadius (c/4) d N by omega) htree)
  have hp:=hparam g o z q hz hfloor (g.Q_im_nonnegative z hz) hold.2.1 htreeEll
  have hsum:(∑i:ι,‖w i‖)≤2*finiteExtraReferenceConstant d*μ:=by
    have hc:(Fintype.card ι:ℝ)=μ:=by
      dsimp only [μ]
      rw [Nat.card_eq_fintype_card]
      exact_mod_cast (Fintype.card_congr labels)
    calc
      _≤∑_i:ι,2*finiteExtraReferenceConstant d:=Finset.sum_le_sum (fun i _=>(hp.2 j _ _).1)
      _=(Fintype.card ι:ℝ)*(2*finiteExtraReferenceConstant d):=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _=2*finiteExtraReferenceConstant d*μ:=by rw [hc];ring
  have he:0≤e:=by
    dsimp only [e,sourceConditionalCellError,sourceCellBadCap,sourceCellEntryCap,
      sourceSelectedMinorConstant,sourceMinorEnlargementConstant,sourceGreenEntryCap,
      sourceGreenPivotCap,eventMass,localSamplingWeight,finiteUniformWeight]
    have hCb:=finiteReferenceConstant_ge_one d hd
    positivity
  have hh:=hdrift' j hjo labels
  have hc:=hcorrection' j hjo
  have htriangle:=norm_sub_le_norm_sub_add_norm_sub
    (finiteComplexMean (fun samples:LocalSamplingFiber g.graph T=>
      (g.labelledResampledGraph T labels samples selector).retainedPhysicalMinor T j z
        (g.truncatedCavityRoot o ell j hjo) (g.truncatedCavityRoot o ell j hjo))-
      cavityIterate z q (ell+1))
    (cavityMeanCorrection g o ell hell j hjo q z) (trivialCavityCorrection N d ell z)
  apply (htriangle.trans (add_le_add hh hc)).trans
  change e*(∑i:ι,‖w i‖)^2+_+_≤e*(2*finiteExtraReferenceConstant d*μ)^2+_+_
  exact add_le_add_right (add_le_add_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hsum 2) he) _) _

end RegularGraph
end SpectralConsequences
