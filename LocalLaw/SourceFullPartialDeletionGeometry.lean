import LocalLaw.PartialDeletedInsideBudget

/-! Actual old partial-inner-deletion class and hereditary diameter.
The inner retained set need not be connected. -/
noncomputable section
namespace LocalLaw
local instance sourceFullPartialDeletionGeometryDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_full_partial_deletion_geometry (a b d:ℕ)(c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d)→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:Fin N)(S:Set (Fin N)),
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      S⊆s.fullTwoTargetVertices (logarithmicRadius (c/4) d N/4) r x y→
      let Tm:Set S:={v|v.val∈T}
      let H:=(g.deficient.restrict S).delete Tm
      let D:=hereditaryReferenceRadius d (fullTwoTargetDiameter d ell r)
      H.ComponentFiniteReferenceBudget ∧ (∀u v,H.graph.dist u v≤D) ∧
      (D:ℝ)+1≤fullRestrictionLogCap d β*Real.log (N:ℝ) ∧
      (hereditaryReferenceRadius d D:ℝ)+1≤fullRestrictionLogCap d β*Real.log (N:ℝ):=by
  filter_upwards [eventually_source_fullTwoTarget_geometry a b d c β B ha hb hd hc hβ hβc,
    eventually_source_fullRestriction_geometry a b d c β B ha hb hd hc hβ hβc] with N hgeo hsubgeo
  intro g o z hz hfloor hballs ι _ labels samples x y S
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let r:=effectiveModelRadius a d N β
  let selector:=logarithmicRadius (c/4) d N/4
  let s:=g.admissibleState T labels samples
  let M:=s.fullTwoTargetVertices selector r x y
  let Tm:Set S:={v|v.val∈T}
  let H:=(g.deficient.restrict S).delete Tm
  let K:Set (Fin N):={v|v∈S∧v∉T}
  intro hSM
  have geo:=(hgeo g o z hz hfloor hballs labels samples x y).1
  have hTM:T⊆M:=by
    intro v hv
    exact Or.inl (Or.inl hv)
  have hbudget:H.ComponentFiniteReferenceBudget:=g.deficient.partial_deleted_inside_component_budget
    M T S (fun _=>rfl) geo.base (graphBall_connected g.graph o ell) hTM hSM Tm (fun _=>Iff.rfl)
  have hKM:K⊆M:=fun _ hv=>hSM hv.1
  have hgeometry:=hsubgeo g o z hz hfloor hballs labels samples x y K hKM
  let e:H.graph≃g g.graph.induce K:=
    { toEquiv:=
        { toFun:=fun v=>⟨v.val.val,v.val.property,v.property⟩
          invFun:=fun v=>⟨⟨v.val,v.property.1⟩,v.property.2⟩
          left_inv:=fun _=>rfl
          right_inv:=fun _=>rfl }
      map_rel_iff':=Iff.rfl }
  refine ⟨hbudget,?_,hgeometry.2.2.1,hgeometry.2.2.2⟩
  intro u v
  rw [←graphIso_dist e u v]
  exact hgeometry.2.1 (e u) (e v)

end RegularGraph
end LocalLaw
