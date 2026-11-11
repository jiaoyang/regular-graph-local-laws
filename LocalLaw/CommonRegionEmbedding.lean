import LocalLaw.SelectedCommonCapture

noncomputable section
namespace LocalLaw
namespace LabelledResamplingState
variable {V:Type}{T:Set V}{ι:Type}[Fintype ι]

def commonRegionEmbedding (s:LabelledResamplingState V T ι)(selector:ℕ)
    (A S:Set (Tᶜ:Set V))(hSA:S⊆A) :
    ((s.partialFirstRemovedSet selector S)ᶜ:Set S) ↪ ((s.partialFirstRemovedSet selector A)ᶜ:Set A) where
  toFun u:=⟨⟨u.val.val,hSA u.val.property⟩,u.property⟩
  inj':=by
    intro u v h
    exact Subtype.ext (Subtype.ext (congrArg (fun w:((s.partialFirstRemovedSet selector A)ᶜ:Set A)=>w.val.val) h))

end LabelledResamplingState
end LocalLaw
