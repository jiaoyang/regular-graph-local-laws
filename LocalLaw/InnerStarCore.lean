import LocalLaw.FiniteStarGeometry
import LocalLaw.SurgeryBallCapture

/-! # The actual two-target sampled-star index is uniformly finite -/

noncomputable section
namespace LocalLaw
local instance innerStarCoreDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type} [Fintype V] {T:Set V} {ι:Type} [Fintype ι]

def innerStarCore (s:LabelledResamplingState V T ι)(selector r:ℕ)(x y:(Tᶜ:Set V)) :
    Set (Tᶜ:Set V) :=
  finiteStarCoreSet (outsideGraph (s.fullResample selector).graph T)
    (s.innerFirstSet selector r x y) x y

theorem innerStarCore_pair_capture (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(hr:1≤r)(x y:(Tᶜ:Set V)) :
    s.innerStarCore selector r x y⊆pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r := by
  apply finiteStarCoreSet_subset
  · exact Or.inl (center_mem_graphBall _ x r)
  · exact Or.inr (center_mem_graphBall _ y r)
  · intro b hb v hv
    exact s.innerFirst_neighbors_captured selector r hr x y b v hb hv

omit [Fintype V] in
theorem innerFirst_pair_capture (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(x y:(Tᶜ:Set V)) :
    s.innerFirstSet selector r x y⊆pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r := by
  intro b hb
  have h:(r-2:ℕ)≤r:=Nat.sub_le _ _
  rcases hb.2 with hx|hy
  · exact Or.inl (hx.trans (ENat.coe_le_coe.mpr h))
  · exact Or.inr (hy.trans (ENat.coe_le_coe.mpr h))

theorem innerStarCore_augmented_capture (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(hr:1≤r)(x y:(Tᶜ:Set V)) :
    s.innerStarCore selector r x y⊆s.twoTargetEndpointVertices selector r x y :=
  (s.innerStarCore_pair_capture selector r hr x y).trans
    (s.twoTargetEndpointVertices_contains_new_pair selector r x y)

theorem innerStarIndex_card (s:LabelledResamplingState V T ι)
    (selector r d:ℕ)(hd:1≤d)(hsep:2*(r-2)≤selector)(x y:(Tᶜ:Set V))
    (hdegree:∀v,(outsideGraph (s.fullResample selector).graph T).degree v≤d) :
    Nat.card (s.innerStarCore selector r x y⊕s.innerFirstSet selector r x y)≤4*d+2 :=
  finiteStarIndex_card_four _ _ x y d hd hdegree (s.innerFirstSet_card selector r hsep x y)

theorem innerStarCore_neighbor (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(x y b v:(Tᶜ:Set V))
    (hb:b∈s.innerFirstSet selector r x y)
    (hvb:(outsideGraph (s.fullResample selector).graph T).Adj b v)
    (hv:v∉s.innerFirstSet selector r x y) : v∈s.innerStarCore selector r x y :=
  finiteStarCoreSet_neighbor _ _ x y b v hb hvb hv

end LabelledResamplingState
end LocalLaw
