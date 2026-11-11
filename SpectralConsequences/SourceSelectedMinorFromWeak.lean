import SpectralConsequences.TreeBoundaryCount
import LocalLaw.SourceOmegaPlusTransferEffective

/-! # Selected-minor replacement from the original weak event alone -/
open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance selectedMinorFromWeakDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceMinorEnlargementConstant (d:ℕ) (β B:ℝ):ℝ:=1+|sourceDeletionConstant d β B|

namespace RegularGraph

theorem eventually_source_weak_tree_sampled_minor_comparison (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32) (hB:0≤B):
    ∀ᶠ N:ℕ in atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let s:=g.admissibleState T labels samples
      let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
      (g.graph.induce T).IsTree→∀i j:s.AdmissibleSampleIndex selector,
      ‖new.G z (s.admissibleSecondVertex selector i) (s.admissibleSecondVertex selector j)-
        sampledDoubleMinor g labels samples selector z i j‖≤
        (2*sourceSelectedMinorConstant d B (sourceMinorEnlargementConstant d β B))*
          (Nat.card (BoundaryOrientedEdge g.graph T):ℝ)*(g.sourcePrime a (logarithmicRadius β d N) z)^2 := by
  let C1:=sourceMinorEnlargementConstant d β B
  have hC1:1≤C1:=by
    dsimp only[C1,sourceMinorEnlargementConstant]
    linarith [abs_nonneg (sourceDeletionConstant d β B)]
  have hCdel:sourceDeletionConstant d β B≤C1:=by
    dsimp only[C1,sourceMinorEnlargementConstant]
    linarith [le_abs_self (sourceDeletionConstant d β B)]
  filter_upwards [eventually_source_tree_sampled_minor_comparison a b d c β B C1 ha hb hd hc hβ hβc hB hC1,
    LocalLaw.RegularGraph.eventually_sourceOmegaWithRadii_subset_sourceOmegaPlusWithRadii a b d c β B C1 (finiteOmega d)
      ha hb hd hc hβ hβc hB hC1 hCdel le_rfl] with N hminor hplus
  intro g o z hz hfloor hzB badCount hold ι _ labels samples
  exact hminor g o z hz hfloor hzB (finiteOmega d) badCount hold
    (hplus g o z badCount hz hzB hfloor hold) labels samples

end RegularGraph
end SpectralConsequences
