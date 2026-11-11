import SpectralConsequences.SourceTraceLabelledDrift
import SpectralConsequences.SourceBoundaryCorrectionSensitivity

/-! Actual labelled trace drift with the physical Section7 correction. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceTracePhysicalDriftDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_trace_physical_drift (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hB:0≤B):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      let selector:=logarithmicRadius (c/4) d N/4
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      let L:=Real.log (N:ℝ)
      ‖finiteComplexMean (fun S:LocalSamplingFiber g.graph T=>
          (g.labelledResampledGraph T labels S selector).G z o o)-
        regularRootValue d ell (g.Q z) z-trivialTraceCorrection N d ell z‖≤
        ‖(treeEdgeWeight d)^2‖*sourceConditionalCellError g a β B labels selector
          (logarithmicRadius β d N) z*(∑i:ι,‖fullBoundaryWeight g o ell (g.Q z) z (labels i)‖)^2+
        traceRootQuadraticConstant d β (sourceMinorEnlargementConstant d β B)*L^(6*a+7)*ε^2+
        boundaryCorrectionSensitivityConstant d β*L^(4*a+1)*scalarScale (spectralScale z) ε*‖trivialPole N d z‖:=by
  filter_upwards [eventually_source_trace_labelled_drift a b d c β B ha hb hd hc hβ hβc hB,
    eventually_source_boundary_correction_sensitivity a b d c β B ha hb hd hc hβ hβc] with N hdrift hsensitivity
  intro g o z hz hfloor hzB badCount hold hTree ι _ labels
  dsimp only
  have hd':=hdrift g o z hz hfloor hzB badCount hold hTree labels
  have hs':=(hsensitivity g o z hz hfloor hzB badCount hold hTree).1
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (traceBoundaryCorrectionCoefficient g o (actualCavityDepth a d N z-1) (g.Q z) z*trivialPole N d z) _).trans
  exact add_le_add hd' hs'

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_source_trace_physical_drift
