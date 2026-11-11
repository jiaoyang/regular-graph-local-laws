import SpectralConsequences.SourceSampledMinorComparison
import LocalLaw.OutsideEdgeCounting

/-! # Tree balls have at least as many outward edge labels as vertices -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance treeBoundaryCountDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}

theorem tree_boundary_dominates_vertices (g:LocalLaw.RegularGraph N d) (hd:3≤d)
    (T:Set (Fin N)) (hT:(g.graph.induce T).IsTree) :
    Nat.card T≤Nat.card (BoundaryOrientedEdge g.graph T) := by
  have hcount:=g.boundary_interior_count T
  have hI : Nat.card (InteriorOrientedEdge g.graph T)=2*(g.graph.induce T).edgeFinset.card := by
    rw [interior_count_induced,Nat.card_eq_fintype_card,(g.graph.induce T).dart_card_eq_twice_card_edges]
  have hE:=hT.card_edgeFinset
  have hV:Fintype.card T=Nat.card T:=(Nat.card_eq_fintype_card).symm
  rw [hV] at hE
  have hdV:=Nat.mul_le_mul_right (Nat.card T) hd
  nlinarith

theorem eventually_source_tree_sampled_minor_comparison (a b d:ℕ) (c β B C1:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32)
    (hB:0≤B) (hC1:1≤C1):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀Cq badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z→
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
        (2*sourceSelectedMinorConstant d B C1)*(Nat.card (BoundaryOrientedEdge g.graph T):ℝ)*
          (g.sourcePrime a (logarithmicRadius β d N) z)^2 := by
  filter_upwards [eventually_source_sampled_minor_comparison a b d c β B C1 ha hb hd hc hβ hβc hB hC1]
    with N hcomp
  intro g o z hz hfloor hzB Cq badCount hold hplus ι _ labels samples
  dsimp only
  intro htree i j
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  have hh:=hcomp g o z hz hfloor hzB Cq badCount hold hplus labels samples i j
  have hn:=tree_boundary_dominates_vertices g hd _ htree
  change Nat.card T≤Nat.card (BoundaryOrientedEdge g.graph T) at hn
  have hr:((Nat.card (BoundaryOrientedEdge g.graph T)+Nat.card T:ℕ):ℝ)≤
      2*(Nat.card (BoundaryOrientedEdge g.graph T):ℝ):=by
    exact_mod_cast (show Nat.card (BoundaryOrientedEdge g.graph T)+Nat.card T≤
      2*Nat.card (BoundaryOrientedEdge g.graph T) by omega)
  apply hh.trans
  have hK:0≤sourceSelectedMinorConstant d B C1:=by dsimp only[sourceSelectedMinorConstant];positivity
  have hbound:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hK) (sq_nonneg (g.sourcePrime a (logarithmicRadius β d N) z))
  exact hbound.trans_eq (by ring)

end RegularGraph
end SpectralConsequences
