import LocalLaw.SourceLeafCompletionGeometry

open Filter
noncomputable section
set_option maxHeartbeats 3000000
namespace LocalLaw
local instance sourceLeafSubsetsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_leaf_completion_geometry_subsets (a d:ℕ)(c β:ℝ)
    (hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32) :
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(ell:ℕ),ell≤doubleLogRadius a d N →
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
      (x y:((graphBallVertices g.graph o ell)ᶜ:Set (Fin N))),
      let T:=graphBallVertices g.graph o ell
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      let S:=s.twoTargetEndpointVertices selector r x y
      let M:=(g.deficient.delete T).restrict S
      let B:=s.partialFirstRemovedSet selector S
      let H:=M.deletedLeafModel (by omega:1≤d) B
      let Rleaf:=hereditaryReferenceRadius d (augmentedObservationDiameter d r)+2
      H.ComponentFiniteReferenceBudget ∧
      (∀u v,H.graph.dist u v≤Rleaf) ∧
      (Rleaf:ℝ)+1≤leafCompletionObservationLogCap d β*Real.log (N:ℝ) ∧
      Nat.card (DeletedLeafIndex M.graph B)≤d*Nat.card (BoundaryOrientedEdge g.graph T) ∧
      (∀l:DeletedLeafIndex M.graph B,(graphBall H.graph (.inr l) r).IsTree) ∧
      (∀l:DeletedLeafIndex M.graph B,∀v∈graphBallVertices H.graph (.inr l) r,H.deficit v=0) ∧
      (∀l m:DeletedLeafIndex M.graph B,l≠m→((2*r:ℕ):ℕ∞)<H.graph.edist (.inr l) (.inr m)) ∧
      ∀K:Set (Bᶜ:Set S),
        let U:=multiLeafLift (deletedLeafMate M.graph B) K
        (H.restrict U).ComponentFiniteReferenceBudget ∧
        (∀a b,(H.restrict U).graph.dist a b≤Rleaf) := by
  filter_upwards [eventually_old_twoTarget_geometry a d c β hd hc hβ hβc,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc]
    with N hgeo hmargin
  intro g o ell hell hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let S:=s.twoTargetEndpointVertices selector r x y
  let M:=(g.deficient.delete T).restrict S
  let B:=s.partialFirstRemovedSet selector S
  let H:=M.deletedLeafModel (by omega:1≤d) B
  let D:=augmentedObservationDiameter d r
  let Rleaf:=hereditaryReferenceRadius d D+2
  have hg:=hgeo g o ell hell hballs labels samples x y
  have hsep:2*r+1≤selector:=by
    have hh:=Nat.mul_le_mul_left 2 hmargin
    dsimp only [r,selector]
    omega
  have hleaf:=g.partialFirst_leaf_geometry (by omega:1≤d) T labels samples selector r hsep S
  have hglobal:=M.leaf_completion_global_local_geometry (by omega:1≤d) B Set.univ hg.1 D hg.2.1
  have hlog:(Rleaf:ℝ)+1≤leafCompletionObservationLogCap d β*Real.log (N:ℝ):=by
    have hR:(Rleaf:ℝ)+1≤(2*(finiteOmega d:ℝ)+7)*((D:ℝ)+1):=by
      dsimp only [Rleaf,hereditaryReferenceRadius]
      push_cast
      nlinarith [Nat.cast_nonneg (α:=ℝ) (finiteOmega d),Nat.cast_nonneg (α:=ℝ) D]
    exact hR.trans ((mul_le_mul_of_nonneg_left hg.2.2 (by positivity)).trans_eq (by
      unfold leafCompletionObservationLogCap
      ring))
  refine ⟨hglobal.1,hglobal.2.2.1,hlog,
    g.partialFirst_deletedLeaf_card_bound T labels samples selector S,
    hleaf.1,hleaf.2.1,hleaf.2.2,?_⟩
  intro K
  have hlocal:=M.leaf_completion_global_local_geometry (by omega:1≤d) B K hg.1 D hg.2.1
  exact ⟨hlocal.2.1,hlocal.2.2.2⟩

end RegularGraph
end LocalLaw
