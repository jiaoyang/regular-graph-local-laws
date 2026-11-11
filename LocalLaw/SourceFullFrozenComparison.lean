import LocalLaw.SourceFullFrozenComparisonOfExterior
import LocalLaw.SourceFullExteriorComparisonProof

/-! The full physical frozen comparison, with its exterior family proved. -/
noncomputable section
namespace LocalLaw.RegularGraph
local instance sourceFullFrozenDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem source_full_frozen_comparison (a b d:ℕ)(c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32):
    ∃D:ℝ,1≤D ∧ ∀ᶠ N:ℕ in Filter.atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→‖z‖≤B→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:Fin N),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let h:=g.labelledResampledGraph T labels samples (logarithmicRadius (c/4) d N/4)
      ‖h.G z x y-h.P (effectiveModelRadius a d N β) z (g.Q z) x y‖≤D/Real.log (N:ℝ):=
  source_full_frozen_comparison_of_exterior a b d c β B ha hb hd hc hβ hβc
    (source_full_exterior_comparison_family a b d c β B 1 ha hb hd hc hβ hβc le_rfl)

end LocalLaw.RegularGraph
