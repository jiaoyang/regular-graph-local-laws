import SpectralConsequences.SourceCavitySiteDrift
import SpectralConsequences.SourceEligibilityProbability
import SpectralConsequences.BallConditionalMaskBounds

/-! The cavity drift on the genuine reversible graph/labels/samples kernel. -/
open scoped BigOperators
open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceCavityConditionalKernelDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def cavitySwitchDrift (N d:ℕ) (o:Fin N) (ell selector:ℕ) (z:ℂ)
    (ω:BallLabelledSpace N d):ℂ:=
  cavityAtVertex (ballLabelledProject (ballLabelledPermutation N d selector ω)).graph d z o-
    (cavityIterate z ((ballLabelledProject ω).Q z) (ell+1)+trivialCavityCorrection N d ell z)

namespace RegularGraph
variable {N d:ℕ}

def sourceCavityUniformDriftError (g:LocalLaw.RegularGraph N d) (a:ℕ) (β B:ℝ)
    (o:Fin N) (ell r:ℕ) (z:ℂ):ℝ:=
  let T:=graphBallVertices g.graph o ell
  sourceConditionalCellUpper g a β B (Equiv.refl (BoundaryOrientedEdge g.graph T)) r z*
      (2*finiteExtraReferenceConstant d*(Nat.card (BoundaryOrientedEdge g.graph T):ℝ))^2+
    cavityRootQuadraticConstant d β (sourceMinorEnlargementConstant d β B)*
      Real.log (N:ℝ)^(6*a+7)*(graphPaperError a d N r z)^2+
    boundaryCorrectionSensitivityConstant d β*Real.log (N:ℝ)^(4*a+1)*
      scalarScale (spectralScale z) (graphPaperError a d N r z)*‖trivialPole N d z‖

theorem eventually_source_cavity_conditional_kernel (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hc1:c≤1/16)
    (hβ:0<β) (hβc:β≤c/32) (hB:0≤B):
    ∀ᶠ N:ℕ in atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree→
      LargeTreeCountAux (4*c) (7*c) g→
      let ell:=actualCavityDepth a d N z-1
      ‖ballLabelledConditionalMean N d o ell
        (cavitySwitchDrift N d o ell (logarithmicRadius (c/4) d N/4) z) g‖≤
        sourceCavityUniformDriftError g a β B o ell (logarithmicRadius β d N) z:=by
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_source_cavity_site_drift a b d c β B ha hb hd hc hβ hβc hB,
    eventually_source_conditional_cell_error_bound a d c β B (by omega) hd hc hc1 hB,
    eventually_resampling_ball_budget a d hd,hdepth,
    eventually_log_ge_nat 1,Filter.eventually_ge_atTop 1]
    with N hdrift hcell hball hdepthN hlog hN
  intro g o z hz hfloor hzB badCount hold htree haux
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let E:=sourceCavityUniformDriftError g a β B o ell (logarithmicRadius β d N) z
  have hε:0≤graphPaperError a d N (logarithmicRadius β d N) z:=graphPaperError_nonnegative _ _ _ _ _ hN hz.le
  have hE:0≤E:=by
    have hC:=finiteReferenceConstant_ge_one d hd
    have hCe:=finiteExtraReferenceConstant_ge_one d hd
    have hA:=sourceObservationLogCap_nonnegative d hd β hβ.le
    have hΨ:=scalarScale_nonneg (s:=spectralScale z) hε
    dsimp only [E,sourceCavityUniformDriftError,sourceConditionalCellUpper,cavityRootQuadraticConstant,
      boundaryQuadraticConstant,sourceCellBadCap,sourceCellEntryCap,sourceSelectedMinorConstant,
      sourceGreenEntryCap,sourceGreenPivotCap,sourceMinorEnlargementConstant,
      boundaryCorrectionSensitivityConstant,truncatedParameterContinuityConstant]
    positivity
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hT:4*Nat.card T≤N:=g.ball_small o ell
    ((Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by omega:0<d+1) hell)).trans hball)
  letI:Nonempty (OutsideOrientedEdge g.graph T):=g.outside_edge_nonempty T (by omega) (by omega) hT
  letI:Nonempty (LocalSamplingFiber g.graph T):=⟨fun _=>Classical.choice inferInstance⟩
  dsimp only
  rw [ballLabelledConditionalMean_prod]
  apply finiteComplexMean_norm_bound_nonnegative _ E hE
  intro labels
  simp only [cavitySwitchDrift,canonicalBallLabelledState_project,canonicalBallLabelledState_permutation_project]
  rw [finiteComplexMean_sub,finiteComplexMean_const]
  have hh:=hdrift g o z hz hfloor hzB badCount hold htree labels
  rw [←sub_add_eq_sub_sub] at hh
  apply hh.trans
  have he:=hcell g o z (logarithmicRadius β d N) haux htree labels
  change sourceConditionalCellError g a β B labels selector (logarithmicRadius β d N) z* _+_+_≤
    sourceConditionalCellUpper g a β B labels (logarithmicRadius β d N) z* _+_+_
  exact add_le_add_right (add_le_add_right (mul_le_mul_of_nonneg_right he (sq_nonneg _)) _) _

end RegularGraph
end SpectralConsequences
