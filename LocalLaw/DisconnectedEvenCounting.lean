import LocalLaw.EvenCycleSpaceExact
import LocalLaw.GeneralGraphEuler

/-!
# Even-pattern counting without graph connectivity

Restricting an even edge pattern to the original connected components
preserves its actual degrees and is injective. The product of the connected
cycle-space counts, together with the proved component Euler identity, gives
the general excess bound needed by disconnected localization targets.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance disconnectedEvenCountingDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) canonicalDisconnectedEvenComponentMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _
variable {V : Type*} [Fintype V]

def evenPatternComponentRestriction (G : SimpleGraph V) (F : EvenEdgeSubgraph G) :
    ∀ C : G.ConnectedComponent, EvenEdgeSubgraph (G.induce C.supp) := fun C =>
  ⟨F.val.induce C.supp, (fun _ _ h => F.property.1 h), by
    intro v
    have hdeg : (F.val.induce C.supp).degree v = F.val.degree v.val :=
      SimpleGraph.degree_induce_of_neighborSet_subset (by
        intro u hu
        exact (C.mem_supp_congr_adj (F.property.1 hu)).mp v.property)
    rw [hdeg]
    exact F.property.2 v.val⟩

theorem evenPatternComponentRestriction_injective (G : SimpleGraph V) :
    Function.Injective (evenPatternComponentRestriction G) := by
  intro F K h
  apply Subtype.ext
  ext u v
  by_cases hconn : G.connectedComponentMk u = G.connectedComponentMk v
  · let C := G.connectedComponentMk u
    let a : C.supp := ⟨u, rfl⟩
    let b : C.supp := ⟨v, hconn.symm⟩
    have hh := congrArg (fun Z : EvenEdgeSubgraph (G.induce C.supp) => Z.val.Adj a b) (congrFun h C)
    exact Iff.of_eq hh
  · have hF : ¬F.val.Adj u v := fun huv => hconn
      (SimpleGraph.ConnectedComponent.sound (F.property.1 huv).reachable)
    have hK : ¬K.val.Adj u v := fun huv => hconn
      (SimpleGraph.ConnectedComponent.sound (K.property.1 huv).reachable)
    simp only [hF, hK]

/-- General finite cycle-space upper bound, sufficient for target graphs
that need not be connected. -/
theorem evenEdgeSubgraph_card_le_excess_general (G : SimpleGraph V) :
    Nat.card (EvenEdgeSubgraph G) ≤ 2 ^ graphExcess G := by
  calc
    _ ≤ Nat.card (∀ C : G.ConnectedComponent, EvenEdgeSubgraph (G.induce C.supp)) :=
      Nat.card_le_card_of_injective (evenPatternComponentRestriction G)
        (evenPatternComponentRestriction_injective G)
    _ = ∏ C : G.ConnectedComponent, Nat.card (EvenEdgeSubgraph (G.induce C.supp)) := Nat.card_pi
    _ ≤ ∏ C : G.ConnectedComponent, 2 ^ graphExcess (G.induce C.supp) :=
      Finset.prod_le_prod' (fun C _ => evenEdgeSubgraph_card_le_excess _ C.connected_induce_supp)
    _ = 2 ^ (∑ C : G.ConnectedComponent, graphExcess (G.induce C.supp)) := Finset.prod_pow_eq_pow_sum _ _ _
    _ = _ := by rw [← graphExcess_eq_sum_components G]

theorem graphExcess_le_of_even_injection_general {U : Type*} [Fintype U]
    (B : SimpleGraph U) (G : SimpleGraph V) (hB : B.Connected)
    (f : EvenEdgeSubgraph B → EvenEdgeSubgraph G) (hf : Function.Injective f) :
    graphExcess B ≤ graphExcess G := by
  have hc := (Nat.card_le_card_of_injective f hf).trans (evenEdgeSubgraph_card_le_excess_general G)
  rw [evenEdgeSubgraph_card_eq_excess B hB] at hc
  by_contra h
  have hh : graphExcess G < graphExcess B := by omega
  have hpow : 2 ^ graphExcess G < 2 ^ graphExcess B := Nat.pow_lt_pow_right (by decide) hh
  omega

end LocalLaw
