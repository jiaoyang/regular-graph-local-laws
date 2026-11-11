import LocalLaw.OmittedLeafData

/-! # Exact multiplicities of all and kept actual omitted leaf slots -/
noncomputable section
namespace LocalLaw
local instance omittedLeafCountsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem embedding_multiplicity_le_deficit {I V:Type*}[Fintype I]
    (e:I↪V)(δ:V→ℕ)(hδ:∀i,1≤δ (e i))(v:V) :
    Nat.card {i:I //e i=v}≤δ v := by
  have hc:Nat.card {i:I //e i=v}≤1:=by
    apply Finite.card_le_one_iff_subsingleton.mpr
    constructor
    intro i j
    exact Subtype.ext (e.injective (i.property.trans j.property.symm))
  by_cases hv:∃i,e i=v
  · obtain ⟨i,hi⟩:=hv
    exact hc.trans (hi ▸ hδ i)
  · haveI:IsEmpty {i:I //e i=v}:=⟨fun i=>hv ⟨i.val,i.property⟩⟩
    simp

namespace LabelledResamplingState
variable {V:Type}[Fintype V]{T:Set V}{ι:Type}[Fintype ι]

instance omittedOldLeavesFintype (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V)) :
    Fintype (s.OmittedOldLeaves selector S) := by unfold OmittedOldLeaves;infer_instance
instance omittedOrdinaryLeavesFintype (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V)) :
    Fintype (s.OmittedOrdinaryLeaves selector S) := by unfold OmittedOrdinaryLeaves;infer_instance
instance omittedExtraLeavesFintype (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V)) :
    Fintype (s.OmittedExtraLeaves selector S) := by unfold OmittedExtraLeaves;infer_instance

def omittedOldFiberEquiv (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V))
    (v:s.OmittedCore selector S) :
    {l:s.OmittedOldLeaves selector S //l.1=v}≃
      {b:s.selectedFirstSet selector //(outsideGraph s.graph T).Adj b.val v.val.val} where
  toFun l:=l.property ▸ l.val.2
  invFun b:=⟨⟨v,b⟩,rfl⟩
  left_inv:=by rintro ⟨⟨w,b⟩,h⟩;cases h;rfl
  right_inv _:=rfl

def omittedOrdinaryFiberEquiv (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V))
    (v:s.OmittedCore selector S) :
    {l:s.OmittedOrdinaryLeaves selector S //l.1=v}≃s.OmittedOrdinarySlot selector S v.val.val where
  toFun l:=l.property ▸ l.val.2
  invFun b:=⟨⟨v,b⟩,rfl⟩
  left_inv:=by rintro ⟨⟨w,b⟩,h⟩;cases h;rfl
  right_inv _:=rfl

def omittedExtraFiberEquiv (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V))
    (v:s.OmittedCore selector S) :
    {i:s.OmittedExtraLeaves selector S //s.omittedExtraRoot selector S i=v}≃
      s.OmittedAddedSlot selector S v.val.val where
  toFun i:=⟨i.val.val,i.val.property.1,
    (congrArg (fun v:s.OmittedCore selector S=>v.val.val) i.property).symm⟩
  invFun i:=⟨⟨i.val,i.property.1,i.property.2 ▸ v.property⟩,
    Subtype.ext (Subtype.ext i.property.2.symm)⟩
  left_inv _:=rfl
  right_inv _:=rfl

def omittedAllFiberEquiv (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V))
    (v:s.OmittedCore selector S) :
    {l:s.OmittedOldLeaves selector S⊕s.OmittedExtraLeaves selector S //s.omittedAllMate selector S l=v}≃
      {l:s.OmittedOldLeaves selector S //l.1=v}⊕
        {i:s.OmittedExtraLeaves selector S //s.omittedExtraRoot selector S i=v} where
  toFun l:=match h:l.val with
    | .inl l'=>.inl ⟨l',show s.omittedAllMate selector S (.inl l')=v from h ▸ l.property⟩
    | .inr i=>.inr ⟨i,show s.omittedAllMate selector S (.inr i)=v from h ▸ l.property⟩
  invFun l:=match l with
    | .inl l=>⟨.inl l.val,l.property⟩
    | .inr i=>⟨.inr i.val,i.property⟩
  left_inv:=by rintro ⟨l,h⟩;cases l <;> rfl
  right_inv:=by intro l;cases l <;> rfl

def omittedKeptFiberEquiv (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V))
    (v:s.OmittedCore selector S) :
    {l:s.OmittedOrdinaryLeaves selector S⊕s.OmittedExtraLeaves selector S //
      s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l)=v}≃
      {l:s.OmittedOrdinaryLeaves selector S //l.1=v}⊕
        {i:s.OmittedExtraLeaves selector S //s.omittedExtraRoot selector S i=v} where
  toFun l:=match h:l.val with
    | .inl l'=>.inl ⟨l',show s.omittedAllMate selector S (s.omittedKeptEmbedding selector S (.inl l'))=v from h ▸ l.property⟩
    | .inr i=>.inr ⟨i,show s.omittedAllMate selector S (s.omittedKeptEmbedding selector S (.inr i))=v from h ▸ l.property⟩
  invFun l:=match l with
    | .inl l=>⟨.inl l.val,l.property⟩
    | .inr i=>⟨.inr i.val,i.property⟩
  left_inv:=by rintro ⟨l,h⟩;cases l <;> rfl
  right_inv:=by intro l;cases l <;> rfl

theorem omittedAllMultiplicity (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V))
    (v:s.OmittedCore selector S) :
    multiLeafMultiplicity (s.omittedAllMate selector S) v=
      Nat.card {b:s.selectedFirstSet selector //(outsideGraph s.graph T).Adj b.val v.val.val}+
        multiLeafMultiplicity (s.omittedExtraRoot selector S) v := by
  rw [multiLeafMultiplicity,Nat.card_congr (s.omittedAllFiberEquiv selector S v),Nat.card_sum,
    Nat.card_congr (s.omittedOldFiberEquiv selector S v)]
  rfl

theorem omittedKeptMultiplicity (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V))
    (v:s.OmittedCore selector S) :
    multiLeafMultiplicity (s.omittedAllMate selector S ∘ s.omittedKeptEmbedding selector S) v=
      Nat.card (s.OmittedOrdinarySlot selector S v.val.val)+Nat.card (s.OmittedAddedSlot selector S v.val.val) := by
  unfold multiLeafMultiplicity
  simp only [Function.comp_apply]
  rw [Nat.card_congr (s.omittedKeptFiberEquiv selector S v),Nat.card_sum,
    Nat.card_congr (s.omittedOrdinaryFiberEquiv selector S v),
    Nat.card_congr (s.omittedExtraFiberEquiv selector S v)]

end LabelledResamplingState
end LocalLaw
