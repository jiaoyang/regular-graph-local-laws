import LocalLaw.FullRegionStarLayout
import LocalLaw.RestrictedDeletedStars

/-! # Actual finite-star reduction on the two literal full-region outside slices -/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance fullRegionStarReductionDecidable (p:Prop):Decidable p:=Classical.propDecidable p
local instance (priority := 2000) fullRegionStarReductionRangeDecidable {L W:Type}(a:L↪W) :
    DecidablePred (fun v:W=>v∈Set.range a):=fun _=>Classical.propDecidable _
namespace LabelledResamplingState
variable {V:Type}[Fintype V][DecidableEq V]{T:Set V}{ι:Type}[Fintype ι]

theorem full_region_star_model_reduction (s:LabelledResamplingState V T ι)
    {d:ℕ}(g:DeficientGraph (Tᶜ:Set V) d)
    (hd:3≤d)(selector r:ℕ)
    (hgraph:g.graph=outsideGraph (s.fullResample selector).graph T)(hr:1≤r)(hsep:2*(r-2)≤selector)(x y:V)(u v:(Tᶜ:Set V))
    (hu:u∈s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r))
    (hv:v∈s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r))
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im) :
    let S₀:=s.fullSliceOutside (s.fullTwoTargetVertices selector r x y)
    let S₁:=s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)
    let A:=s.fullRegionOuterFirst selector r x y
    let I:=s.fullRegionStarCore selector r x y u v
    let J:=s.fullRegionInnerFirst selector r x y
    let H:=s.fullRegionStarLayout selector r hr x y u v hu hv
    let g₀:=(g.restrict S₀).delete {v:S₀|v.val∈A}
    let g₁:=(g.restrict S₁).delete {v:S₁|v.val∈A}
    let a:=restrictedStarInner S₀ A J H.inner_left H.inner_not_outer
    let b:=restrictedStarInner S₁ A J H.inner_right H.inner_not_outer
    let e:=restrictedStarCore S₀ A I J H.core_left H.core_not_outer H.inner_left H.inner_not_outer H.core_not_inner
    let f:=restrictedStarCore S₁ A I J H.core_right H.core_not_outer H.inner_right H.inner_not_outer H.core_not_inner
    let R:=((g₀.delete (Set.range a)).extensionGreen q z).submatrix e e
    let P:=((g₁.delete (Set.range b)).extensionGreen q z).submatrix f f
    let GM:=(g₀.extensionGreen q z).submatrix (embeddedStarEmbedding a e) (embeddedStarEmbedding a e)
    let GN:=(g₁.extensionGreen q z).submatrix (embeddedStarEmbedding b f) (embeddedStarEmbedding b f)
    Nat.card (I⊕J)≤4*d+2 ∧ IsUnit R ∧ IsUnit P ∧
      GM-GN=(GM.submatrix id Sum.inl*R⁻¹)*(R-P)*(P⁻¹*GN.submatrix Sum.inl id) := by
  dsimp only
  let H:=s.fullRegionStarLayout selector r hr x y u v hu hv
  have hdeg:∀v,(outsideGraph (s.fullResample selector).graph T).degree v≤d:=by
    intro v
    rw [←hgraph]
    exact g.degree_le v
  refine ⟨s.fullRegionStarIndex_card selector r d (by omega) x y u v hsep hdeg,?_⟩
  apply g.restricted_deleted_star_difference hd _ _ _ _ _ H.core_left H.core_right H.inner_left H.inner_right
    H.core_not_outer H.inner_not_outer H.core_not_inner ?_ ?_ ?_ q z hz hq
  · simpa only [hgraph] using H.capture_left
  · simpa only [hgraph] using H.capture_right
  · simpa only [hgraph] using H.neighbor_core


end LabelledResamplingState
end LocalLaw
