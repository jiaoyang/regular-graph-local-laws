import LocalLaw.EvenPatternRestriction
import LocalLaw.BallEvenPatternGeometry

/-!
# Excess transfer from actual localized even edge patterns

If every even edge pattern in B maps into G and has its supported vertices
in S, mapping followed by actual restriction injects the entire even-pattern
space into the even-pattern space of G[S]. Exact cycle-space cardinalities
then give the excess inequality. The map, support restriction, and injection
are constructed in the proof.
-/

noncomputable section
set_option maxHeartbeats 1600000
namespace LocalLaw

local instance evenPatternTransferDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {U V : Type*} [Fintype U] [Fintype V]

theorem graphExcess_le_of_even_pattern_localization (B : SimpleGraph U) (G : SimpleGraph V)
    (emb : U ↪ V) (S : Set V) (hB : B.Connected) (hS : (G.induce S).Connected)
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
  have hconn : (G.comap inc).Connected := hS
  have hbound := connected_graphExcess_le_of_even_injection B (G.comap inc) hB hconn f hf
  simp only [graphExcess, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hbound ⊢
  exact hbound

end LocalLaw
