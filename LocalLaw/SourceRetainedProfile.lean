import LocalLaw.SourceRetainedRowProfile
import LocalLaw.SourceRetainedEntries

/-! # Transfer the actual expanded-ball profile to the fixed retained kernel -/

noncomputable section
namespace LocalLaw
local instance sourceRetainedProfileDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_retained_profile (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let r := effectiveModelRadius a d N β
      let root : T := ⟨o,center_mem_graphBall g.graph o _⟩
      Nonempty (BoundaryMaxProfile (g.sourceRetainedReference T r (g.Q z) z)
        (fun α => cutInsideVertex g.graph T (labels α)) root a (Real.log (N:ℝ))
        ((d:ℝ)*((d:ℝ)+1)) (2*finiteExtraReferenceConstant d*((d:ℝ)+1))
        (8*(d:ℝ)*finiteExtraReferenceConstant d^2*sourceObservationLogCap d β)) := by
  filter_upwards [eventually_source_retained_row_profile a b d c β B C1 ha hb hd hc hβ hβc hC1]
    with N hbase
  intro g o z hz hfloor Cq badCount hplus ι _ labels
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let S := graphBallVertices g.graph o (ell+r+1)
  let hS : T ⊆ S := graphBallVertices_mono g.graph o (by omega)
  let K := (g.deficient.restrict S).extensionGreen (g.Q z) z
  let rootS : S := ⟨o,hS (center_mem_graphBall g.graph o ell)⟩
  let rootT : T := ⟨o,center_mem_graphBall g.graph o ell⟩
  let lS := inducedBoundaryInner g.graph o ell S hS
  let lT := fun α => cutInsideVertex g.graph T (labels α)
  let e : T → S := fun x => ⟨x.val,hS x.property⟩
  obtain ⟨profile⟩ := hbase g o z hz hfloor Cq badCount hplus
  let transferred := profile.pullback K lS rootS a (Real.log (N:ℝ))
    ((d:ℝ)*((d:ℝ)+1)) (2*finiteExtraReferenceConstant d*((d:ℝ)+1))
    (8*(d:ℝ)*finiteExtraReferenceConstant d^2*sourceObservationLogCap d β)
    e labels lT rootT rfl (fun _ => rfl)
  have heq : K.submatrix e e=g.sourceRetainedReference T r (g.Q z) z := by
    ext x y
    exact (g.sourceRetainedReference_entry_expanded_ball o ell r (g.Q z) z x y).symm
  rw [heq] at transferred
  exact ⟨transferred⟩

end RegularGraph
end LocalLaw
