import LocalLaw.InnerStarModelReduction

/-! # Actual target labels in the finite sampled-star matrix -/

noncomputable section
namespace LocalLaw
local instance finiteStarTargetsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type}

def starTargetIndex (I J:Set V)(v:V)(hcover:v∈I∨v∈J) : I⊕J :=
  if h:v∈I then Sum.inl ⟨v,h⟩ else Sum.inr ⟨v,hcover.resolve_left h⟩

theorem restrictedStarTarget_value (S A I J:Set V)(hIS:I⊆S)(hIA:∀v∈I,v∉A)
    (hJS:J⊆S)(hJA:∀v∈J,v∉A)(hIJ:∀v∈I,v∉J)(v:V)(hcover:v∈I∨v∈J) :
    (embeddedStarEmbedding (restrictedStarInner S A J hJS hJA)
      (restrictedStarCore S A I J hIS hIA hJS hJA hIJ)
      (starTargetIndex I J v hcover)).val.val=v := by
  unfold starTargetIndex
  split <;> rfl

namespace LabelledResamplingState
variable [Fintype V] {T:Set V} {ι:Type} [Fintype ι]

theorem innerStarDeletedCore_targets (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(x y:(Tᶜ:Set V)) :
    (x∈s.innerStarDeletedCore selector r x y ∨ x∈s.innerFirstSet selector r x y) ∧
    (y∈s.innerStarDeletedCore selector r x y ∨ y∈s.innerFirstSet selector r x y) := by
  have hout:=s.outerFirst_targets_not_mem selector r x y
  have htargets:=finiteStarCoreSet_targets (outsideGraph (s.fullResample selector).graph T)
    (s.innerFirstSet selector r x y) x y
  constructor
  · by_cases hx:x∈s.innerFirstSet selector r x y
    · exact Or.inr hx
    · exact Or.inl ⟨htargets.1 hx,hout.1⟩
  · by_cases hy:y∈s.innerFirstSet selector r x y
    · exact Or.inr hy
    · exact Or.inl ⟨htargets.2 hy,hout.2⟩

end LabelledResamplingState
end LocalLaw
