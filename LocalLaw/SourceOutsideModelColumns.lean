import LocalLaw.SingleTargetOutsideLocality
import LocalLaw.FilledOutsideColumns
import LocalLaw.LocalizationWeakBudgets

/-! # Actual constant outside-model boundary columns with source parameters -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceOutsideModelColumnsDecidable (p:Prop) : Decidable p := Classical.propDecidable p

def sourceOutsideModelColumnConstant (d:ℕ) : ℝ := 2*finiteExtraReferenceConstant d*(finiteOmega d+1)

namespace RegularGraph

theorem eventually_source_outside_model_column (a b d:ℕ) (c β B C1:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32) (hC1:1≤C1) :
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀Cq badCount:ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell:=actualCavityDepth a d N z-1
      let R:=logarithmicRadius (c/4) d N
      let T:=graphBallVertices g.graph o ell
      let r:=effectiveModelRadius a d N β
      let gnew:=g.labelledResampledGraph T labels samples (R/4)
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) R (finiteOmega d) badCount z →
      ∀(y:Fin N)(hy:y∉T),
      let K:=g.singleTargetOutsideVertices T labels samples (R/4) r y
      let hK:=g.singleTargetOutside_boundary_capture T labels samples (R/4) r y
      let j:=g.singleTargetOutsideTargetVertex T labels samples (R/4) r y hy
      let Q:=((gnew.deficient.delete T).restrict K).extensionGreen (gnew.Q z) z
      (∑α:BoundaryOrientedEdge gnew.graph T,‖Q (gnew.filledBoundaryVertex T K hK α) j‖)≤sourceOutsideModelColumnConstant d ∧
      (∑α:BoundaryOrientedEdge gnew.graph T,‖Q (gnew.filledBoundaryVertex T K hK α) j‖)≤sourceOutsideModelColumnConstant d*Real.log (N:ℝ) := by
  let A:=singleTargetFilledLogCap d β
  have hAobs:=sourceObservationLogCap_nonnegative d hd β hβ.le
  have hCextra:0≤finiteExtraReferenceConstant d:=(by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hA:0≤A := by dsimp only [A,singleTargetFilledLogCap,filledEndpointLogCap]; positivity
  filter_upwards [eventually_singleTargetFilled_geometry a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_log_ge_nat (DeficientGraph.localizationBudgetConstant d B A)] with N hgeom hnum hlarge
  intro g o z hz hfloor Cq badCount hplus ι _ labels samples
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let R:=logarithmicRadius (c/4) d N
  let T:=graphBallVertices g.graph o ell
  let r:=effectiveModelRadius a d N β
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let gnew:=g.labelledResampledGraph T labels samples (R/4)
  let s:=g.admissibleState T labels samples
  intro htarget y hy
  let K:=g.singleTargetOutsideVertices T labels samples (R/4) r y
  let hK:=g.singleTargetOutside_boundary_capture T labels samples (R/4) r y
  let j:=g.singleTargetOutsideTargetVertex T labels samples (R/4) r y hy
  let Rfull:=singleTargetFilledDiameter d ell r
  have geom:=g.singleTargetOutside_geometry T labels samples (R/4) r y Rfull A L
    (hgeom g o z hz hfloor Cq badCount hplus labels samples htarget y)
  have num:=hnum z hz hfloor
  have hε:0≤ε:=num.error_nonnegative
  have hεs:0≤C1^2*ε:=mul_nonneg (sq_nonneg C1) hε
  have habs:=scalarScale_constant_absorption (spectralScale z) ε C1 (spectralScale_pos hz) hε hC1
  have hprior:‖gnew.Q z-semicircleRoot z‖≤scalarScale (spectralScale z) (C1^2*ε):=
    htarget.2.1.trans ((le_mul_of_one_le_left (scalarScale_nonneg hε) hC1).trans habs)
  have hsmall:‖gnew.Q z-semicircleRoot z‖*finiteExtraReferenceConstant d*coreConvolutionConstant (finiteOmega d+1)*
      (((finiteOmega d+1)*(2*Rfull+1):ℕ)+1:ℝ)≤1/2 :=
    (DeficientGraph.weak_localization_feedback_budgets d hd z (gnew.Q z) hz B (C1^2*ε) L A hεs num.log_one hA
      num.error_scaled hprior Rfull Rfull geom.diameter_log geom.diameter_log hlarge).2.2.1
  have hTconn:(gnew.graph.induce T).Connected:=by
    rw [show gnew.graph.induce T=g.graph.induce T from s.fullResample_induce (R/4)]
    exact graphBall_connected g.graph o ell
  have hcol:=gnew.filledOutside_boundary_column hd T K hK hTconn geom.base Rfull geom.diameter
    (gnew.Q z) z hz (gnew.Q_im_nonnegative z hz) hsmall j
  constructor
  · exact hcol
  · exact hcol.trans (le_mul_of_one_le_right (by positivity) num.log_one)

end RegularGraph
end LocalLaw
