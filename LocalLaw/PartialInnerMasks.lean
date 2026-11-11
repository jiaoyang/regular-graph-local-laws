import LocalLaw.PartialEndpointMasks

/-! Actual outside endpoint indices after deleting the retained inner vertices. -/
noncomputable section
namespace LocalLaw
local instance partialInnerMasksDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type}{T:Set V}{ι:Type}

def fullSliceOutside (_s:LabelledResamplingState V T ι)(S:Set V):Set (Tᶜ:Set V):={v|v.val∈S}
def retainedInnerLabels (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set V):
    Set (s.AdmissibleSampleIndex selector):={i|(s.quad i.val).a∈S}
def retainedInnerSet (_s:LabelledResamplingState V T ι)(S:Set V):Set S:={v|v.val∈T}

def partialInnerDeletedEmbedding (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set V):
    s.PartialEndpointIndex selector (s.fullSliceOutside S)↪((s.retainedInnerSet S)ᶜ:Set S) where
  toFun u:=
    let v:=s.partialEndpointEmbedding selector (s.fullSliceOutside S) u
    ⟨⟨v.val.val,v.property⟩,v.val.property⟩
  inj' u v huv:=by
    apply (s.partialEndpointEmbedding selector (s.fullSliceOutside S)).injective
    exact Subtype.ext (Subtype.ext (congrArg (fun t:((s.retainedInnerSet S)ᶜ:Set S)=>t.val.val) huv))

theorem partialInnerDeletedEmbedding_val (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set V)
    (u:s.PartialEndpointIndex selector (s.fullSliceOutside S)):
    (s.partialInnerDeletedEmbedding selector S u).val.val=
      (s.partialEndpointEmbedding selector (s.fullSliceOutside S) u).val.val:=rfl

end LabelledResamplingState
end LocalLaw
