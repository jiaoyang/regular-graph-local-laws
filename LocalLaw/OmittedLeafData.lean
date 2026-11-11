import LocalLaw.OmittedLeafEmbedding
import LocalLaw.PartialEndpointMasks

/-! # The actual complete and kept leaf families for an omitted switch

The common core has every selected B vertex removed. Ordinary kept slots
embed into literal old B-neighbor incidences; added slots attach at the
actual A vertex of each omitted B. These are concrete source index types.
-/

noncomputable section
namespace LocalLaw
local instance omittedLeafDataDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type}[Fintype V]{T:Set V}{ι:Type}[Fintype ι]

omit [Fintype V] [Fintype ι] in
theorem admissibleBoundaryVertex_not_selectedFirst (s:LabelledResamplingState V T ι)
    (selector:ℕ)(i:s.AdmissibleSampleIndex selector) :
    s.admissibleBoundaryVertex selector i∉s.selectedFirstSet selector := by
  rintro ⟨j,hj⟩
  have he:s.admissibleTripleVertex selector (i,0)=s.admissibleTripleVertex selector (j,1):=by
    simpa only [admissibleTripleVertex,outsideTripleVertex,admissibleBoundaryVertex,
      admissibleSampleVertex] using hj.symm
  have hc:=s.admissibleTripleVertex_injective selector he
  have hn:=congrArg (fun p:s.AdmissibleSampleIndex selector×Fin 3=>p.2.val) hc
  norm_num at hn

omit [Fintype V] [Fintype ι] in
theorem admissibleBoundaryVertex_injective (s:LabelledResamplingState V T ι)(selector:ℕ) :
    Function.Injective (s.admissibleBoundaryVertex selector) := by
  intro i j h
  have he:s.admissibleTripleVertex selector (i,0)=s.admissibleTripleVertex selector (j,0):=h
  exact congrArg Prod.fst (s.admissibleTripleVertex_injective selector he)

abbrev OmittedCore (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V)) :=
  {v:((s.selectedFirstSet selector)ᶜ:Set (Tᶜ:Set V)) //v.val∈S}

def OmittedOldLeaves (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V)) :=
  Σv:s.OmittedCore selector S,{b:s.selectedFirstSet selector //(outsideGraph s.graph T).Adj b.val v.val.val}

def OmittedOrdinaryLeaves (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V)) :=
  Σv:s.OmittedCore selector S,s.OmittedOrdinarySlot selector S v.val.val

def OmittedExtraLeaves (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V)) :=
  {i:s.AdmissibleSampleIndex selector //s.admissibleSampleVertex selector i∉S ∧
    s.admissibleBoundaryVertex selector i∈S}

def omittedExtraRoot (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V)) :
    s.OmittedExtraLeaves selector S↪s.OmittedCore selector S where
  toFun i:=⟨⟨s.admissibleBoundaryVertex selector i.val,
    s.admissibleBoundaryVertex_not_selectedFirst selector i.val⟩,i.property.2⟩
  inj':=by
    intro i j h
    exact Subtype.ext (s.admissibleBoundaryVertex_injective selector
      (congrArg (fun v:s.OmittedCore selector S=>v.val.val) h))

def omittedOrdinaryOldEmbedding (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V)) :
    s.OmittedOrdinaryLeaves selector S↪s.OmittedOldLeaves selector S where
  toFun p:=⟨p.1,⟨⟨s.admissibleSampleVertex selector p.2.val,⟨p.2.val,rfl⟩⟩,p.2.property.2.1⟩⟩
  inj':=by
    rintro ⟨v,i⟩ ⟨w,j⟩ h
    have hv:v=w:=congrArg Sigma.fst h
    subst w
    have hi:(s.selectedFirstEmbedding selector i.val)=(s.selectedFirstEmbedding selector j.val):=
      congrArg (fun p:s.OmittedOldLeaves selector S=>p.2.val.val) h
    have hij:i=j:=Subtype.ext ((s.selectedFirstEmbedding selector).injective hi)
    subst j
    rfl

def omittedAllMate (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V)) :
    s.OmittedOldLeaves selector S⊕s.OmittedExtraLeaves selector S→s.OmittedCore selector S :=
  Sum.elim Sigma.fst (s.omittedExtraRoot selector S)

def omittedKeptEmbedding (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V)) :
    (s.OmittedOrdinaryLeaves selector S⊕s.OmittedExtraLeaves selector S)↪
      (s.OmittedOldLeaves selector S⊕s.OmittedExtraLeaves selector S) :=
  (s.omittedOrdinaryOldEmbedding selector S).sumMap (Function.Embedding.refl _)

end LabelledResamplingState
end LocalLaw
