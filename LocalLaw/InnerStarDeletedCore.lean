import LocalLaw.InnerStarCore

/-! # The finite inner-star core after deleting outer selected vertices -/

noncomputable section
namespace LocalLaw
local instance innerStarDeletedDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type} [Fintype V] {T:Set V} {ι:Type} [Fintype ι]

def innerStarDeletedCore (s:LabelledResamplingState V T ι)(selector r:ℕ)(x y:(Tᶜ:Set V)) :
    Set (Tᶜ:Set V) :=
  s.innerStarCore selector r x y\s.outerFirstSet selector r x y

omit [Fintype V] in
theorem innerFirst_not_outer (s:LabelledResamplingState V T ι)(selector r:ℕ)(x y:(Tᶜ:Set V)) :
    ∀v∈s.innerFirstSet selector r x y,v∉s.outerFirstSet selector r x y := by
  intro v hv ho
  exact ho.2 hv.2

theorem innerStarDeletedCore_geometry (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(hr:1≤r)(x y:(Tᶜ:Set V)) :
    let I:=s.innerStarDeletedCore selector r x y
    let J:=s.innerFirstSet selector r x y
    let A:=s.outerFirstSet selector r x y
    let S₀:=s.twoTargetEndpointVertices selector r x y
    let S₁:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
    I⊆S₀ ∧ I⊆S₁ ∧ J⊆S₀ ∧ J⊆S₁ ∧
      (∀v∈I,v∉A) ∧ (∀v∈J,v∉A) ∧ (∀v∈I,v∉J) ∧
      (∀b∈J,∀v,(outsideGraph (s.fullResample selector).graph T).Adj b v→v∈S₀) ∧
      (∀b∈J,∀v,(outsideGraph (s.fullResample selector).graph T).Adj b v→v∈S₁) ∧
      (∀b∈J,∀v,(outsideGraph (s.fullResample selector).graph T).Adj b v→v∉A→v∉J→v∈I) := by
  dsimp only
  have hIS:=s.innerStarCore_pair_capture selector r hr x y
  have hJS:=s.innerFirst_pair_capture selector r x y
  have haug:=s.twoTargetEndpointVertices_contains_new_pair selector r x y
  refine ⟨fun _ h=>haug (hIS h.1),fun _ h=>hIS h.1,
    fun _ h=>haug (hJS h),hJS,fun _ h=>h.2,s.innerFirst_not_outer selector r x y,?_,?_,?_,?_⟩
  · intro v hv
    exact finiteStarCoreSet_not_mem _ _ x y v hv.1
  · intro b hb v hv
    exact haug (s.innerFirst_neighbors_captured selector r hr x y b v hb hv)
  · intro b hb v hv
    exact s.innerFirst_neighbors_captured selector r hr x y b v hb hv
  · intro b hb v hv hA hJ
    exact ⟨s.innerStarCore_neighbor selector r x y b v hb hv hJ,hA⟩

theorem innerStarDeletedIndex_card (s:LabelledResamplingState V T ι)
    (selector r d:ℕ)(hd:1≤d)(hsep:2*(r-2)≤selector)(x y:(Tᶜ:Set V))
    (hdegree:∀v,(outsideGraph (s.fullResample selector).graph T).degree v≤d) :
    Nat.card (s.innerStarDeletedCore selector r x y⊕s.innerFirstSet selector r x y)≤4*d+2 := by
  have hI:Nat.card (s.innerStarDeletedCore selector r x y)≤Nat.card (s.innerStarCore selector r x y):=
    Nat.card_le_card_of_injective (fun v=>⟨v.val,v.property.1⟩)
      (fun _ _ h=>Subtype.ext (congrArg (fun v:s.innerStarCore selector r x y=>v.val) h))
  have h:=s.innerStarIndex_card selector r d hd hsep x y hdegree
  rw [Nat.card_sum] at h ⊢
  omega

end LabelledResamplingState
end LocalLaw
