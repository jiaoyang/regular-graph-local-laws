import LocalLaw.InnerSelectedGeometry
import LocalLaw.PartialFirstDeletionCaps

/-! # Literal outer selected vertices are far from the retained targets -/

noncomputable section
namespace LocalLaw
local instance outerFirstRegionGeometryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type} [Fintype ι]

def outerFirstRegion (s : LabelledResamplingState V T ι)(selector r : ℕ)
    (x y : (Tᶜ:Set V))(S : Set (Tᶜ:Set V)) : Set S :=
  {v | v.val∈s.outerFirstSet selector r x y}

theorem outerFirstRegion_subset_removed (s : LabelledResamplingState V T ι)(selector r : ℕ)
    (x y : (Tᶜ:Set V))(S : Set (Tᶜ:Set V)) :
    s.outerFirstRegion selector r x y S⊆s.partialFirstRemovedSet selector S :=
  fun _ hv => hv.1

theorem outerFirstRegion_targets_not_mem (s : LabelledResamplingState V T ι)(selector r : ℕ)
    (x y : (Tᶜ:Set V))(S : Set (Tᶜ:Set V))(hx:x∈S)(hy:y∈S) :
    (⟨x,hx⟩:S)∉s.outerFirstRegion selector r x y S ∧
      (⟨y,hy⟩:S)∉s.outerFirstRegion selector r x y S :=
  s.outerFirst_targets_not_mem selector r x y

theorem outerFirstRegion_far (s : LabelledResamplingState V T ι)(selector r : ℕ)
    (x y : (Tᶜ:Set V))(S : Set (Tᶜ:Set V))(hx:x∈S)(hy:y∈S)
    (b:s.outerFirstRegion selector r x y S) :
    (((r-2)+1:ℕ):ℕ∞)≤((outsideGraph (s.fullResample selector).graph T).induce S).edist ⟨x,hx⟩ b.val ∧
      (((r-2)+1:ℕ):ℕ∞)≤((outsideGraph (s.fullResample selector).graph T).induce S).edist ⟨y,hy⟩ b.val := by
  let G:=outsideGraph (s.fullResample selector).graph T
  have hnot : b.val.val∉pairBallVertices G x y (r-2) := b.property.2
  have hxfar : (((r-2)+1:ℕ):ℕ∞)≤G.edist x b.val.val := by
    have hh : ((r-2:ℕ):ℕ∞)<G.edist x b.val.val := lt_of_not_ge (fun h => hnot (Or.inl h))
    simpa only [Nat.cast_add,Nat.cast_one] using (ENat.add_one_le_iff (ENat.coe_ne_top _)).mpr hh
  have hyfar : (((r-2)+1:ℕ):ℕ∞)≤G.edist y b.val.val := by
    have hh : ((r-2:ℕ):ℕ∞)<G.edist y b.val.val := lt_of_not_ge (fun h => hnot (Or.inr h))
    simpa only [Nat.cast_add,Nat.cast_one] using (ENat.add_one_le_iff (ENat.coe_ne_top _)).mpr hh
  exact ⟨hxfar.trans (graphHom_edist_le (SimpleGraph.Embedding.induce (G:=G) S).toHom ⟨x,hx⟩ b.val),
    hyfar.trans (graphHom_edist_le (SimpleGraph.Embedding.induce (G:=G) S).toHom ⟨y,hy⟩ b.val)⟩

variable [Fintype V]

theorem outerFirstRegion_card (s : LabelledResamplingState V T ι)(selector r : ℕ)
    (x y : (Tᶜ:Set V))(S : Set (Tᶜ:Set V)) :
    Nat.card (s.outerFirstRegion selector r x y S)≤Nat.card (s.AdmissibleSampleIndex selector) := by
  let e : s.outerFirstRegion selector r x y S ↪ s.partialFirstRemovedSet selector S :=
    {toFun:=fun v=>⟨v.val,s.outerFirstRegion_subset_removed selector r x y S v.property⟩
     inj':=by
       intro u v h
       have hh:u.val=v.val:=congrArg (fun w:s.partialFirstRemovedSet selector S=>w.val) h
       exact Subtype.ext hh}
  exact (Nat.card_le_card_of_injective e e.injective).trans
    (by
      rw [←Nat.card_congr (s.partialFirstRemovalEquiv selector S)]
      exact Nat.card_le_card_of_injective (Subtype.val:s.partialFirstMask selector S→s.AdmissibleSampleIndex selector)
        Subtype.val_injective)

end LabelledResamplingState
end LocalLaw
