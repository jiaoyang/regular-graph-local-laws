import LocalLaw.DisconnectedEvenCounting
import LocalLaw.EvenPatternTransfer

/-!
# Excess transfer into a possibly disconnected localization target

The actual map/restriction injection is combined with the general component
counting upper bound. Only the source ball must be connected; no target
connectivity premise is needed.
-/

noncomputable section
set_option maxHeartbeats 1600000
namespace LocalLaw
local instance disconnectedEvenTransferDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {U V : Type*} [Fintype U] [Fintype V]
theorem graphExcess_le_of_even_pattern_localization_general (B : SimpleGraph U) (G : SimpleGraph V)
    (emb : U ↪ V) (S : Set V) (hB : B.Connected)
    (hedges : ∀ C : EvenEdgeSubgraph B, C.val.map emb ≤ G)
    (hsupport : ∀ C : EvenEdgeSubgraph B, (C.val.map emb).support ⊆ S) :
    graphExcess B ≤ graphExcess (G.induce S) := by
  let inc : S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let ambient : EvenEdgeSubgraph B → SupportedEvenSubgraph G (Set.range inc) := fun C =>
    ⟨⟨C.val.map emb, hedges C, by
      have h := mapped_even_pattern C.val emb C.property.2
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using h⟩,
      fun x hx => ⟨⟨x, hsupport C hx⟩, rfl⟩⟩
  have hambient : Function.Injective ambient := by
    intro C D h
    have heq : C.val.map emb = D.val.map emb :=
      congrArg (fun F : SupportedEvenSubgraph G (Set.range inc) => F.val.val) h
    exact Subtype.ext (SimpleGraph.map_injective emb heq)
  let f := (restrictSupportedEvenSubgraph G inc) ∘ ambient
  have hf : Function.Injective f := (restrictSupportedEvenSubgraph_injective G inc).comp hambient
  have hbound := graphExcess_le_of_even_injection_general B (G.comap inc) hB f hf
  simp only [graphExcess, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hbound ⊢
  exact hbound

end LocalLaw
