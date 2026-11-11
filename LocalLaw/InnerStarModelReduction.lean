import LocalLaw.InnerStarDeletedCore
import LocalLaw.RestrictedDeletedStars

/-! # Actual sampled-star reduction between the common and literal pair models

The core may carry different omitted-outer-neighbor deficits on the two sides.
The finite index contains only the two targets and neighbors of at most two
inner sampled vertices; its size is at most 4d+2.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance innerStarModelDecidable (p:Prop):Decidable p:=Classical.propDecidable p
local instance (priority := 2000) innerStarModelRangeDecidable {L W:Type} (a:L↪W) :
    DecidablePred (fun v:W=>v∈Set.range a) := fun _=>Classical.propDecidable _

structure CapturedStarLayout {V:Type}(G:SimpleGraph V)(S₀ S₁ A I J:Set V) : Prop where
  core_left : I⊆S₀
  core_right : I⊆S₁
  inner_left : J⊆S₀
  inner_right : J⊆S₁
  core_not_outer : ∀v∈I,v∉A
  inner_not_outer : ∀v∈J,v∉A
  core_not_inner : ∀v∈I,v∉J
  capture_left : ∀b∈J,∀v,G.Adj b v→v∈S₀
  capture_right : ∀b∈J,∀v,G.Adj b v→v∈S₁
  neighbor_core : ∀b∈J,∀v,G.Adj b v→v∉A→v∉J→v∈I

namespace LabelledResamplingState
variable {V:Type} [Fintype V] {T:Set V} {ι:Type} [Fintype ι]

theorem innerStarLayout (s:LabelledResamplingState V T ι)(selector r:ℕ)(hr:1≤r)
    (x y:(Tᶜ:Set V)) :
    CapturedStarLayout (outsideGraph (s.fullResample selector).graph T)
      (s.twoTargetEndpointVertices selector r x y)
      (pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r)
      (s.outerFirstSet selector r x y) (s.innerStarDeletedCore selector r x y)
      (s.innerFirstSet selector r x y) := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀⟩:=s.innerStarDeletedCore_geometry selector r hr x y
  exact ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀⟩

/-- A concrete actual graph model with the switched outside adjacency.
All precision matching and all inverse units are conclusions. -/
theorem inner_star_model_reduction (s:LabelledResamplingState V T ι)
    {d:ℕ}(g:DeficientGraph (Tᶜ:Set V) d)
    (hd:3≤d)(selector r:ℕ)
    (hgraph:g.graph=outsideGraph (s.fullResample selector).graph T)(hr:1≤r)(hsep:2*(r-2)≤selector)(x y:(Tᶜ:Set V))
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im) :
    let S₀:=s.twoTargetEndpointVertices selector r x y
    let S₁:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
    let A:=s.outerFirstSet selector r x y
    let I:=s.innerStarDeletedCore selector r x y
    let J:=s.innerFirstSet selector r x y
    let H:=s.innerStarLayout selector r hr x y
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
  let H:=s.innerStarLayout selector r hr x y
  have hdeg:∀v,(outsideGraph (s.fullResample selector).graph T).degree v≤d:=by
    intro v
    rw [←hgraph]
    exact g.degree_le v
  refine ⟨s.innerStarDeletedIndex_card selector r d (by omega) hsep x y hdeg,?_⟩
  apply g.restricted_deleted_star_difference hd _ _ _ _ _ H.core_left H.core_right H.inner_left H.inner_right
    H.core_not_outer H.inner_not_outer H.core_not_inner ?_ ?_ ?_ q z hz hq
  · simpa only [hgraph] using H.capture_left
  · simpa only [hgraph] using H.capture_right
  · simpa only [hgraph] using H.neighbor_core

end LabelledResamplingState
end LocalLaw
