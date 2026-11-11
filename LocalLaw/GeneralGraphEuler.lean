import LocalLaw.ExcessCutset

/-!
# Euler's excess identity without a connectivity assumption

Actual connected-component vertex and dart equivalences give the natural
subtraction guard and the sum of component excesses. No component count or
Euler equality is supplied as a hypothesis.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance generalEulerDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) canonicalGeneralEulerComponentMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _
variable {V : Type*} [Fintype V]

theorem graph_component_vertex_count (G : SimpleGraph V) :
    (∑ C : G.ConnectedComponent, Nat.card C.supp) = Nat.card V := by
  rw [← Nat.card_sigma]
  exact Nat.card_congr (componentVertexEquiv G)

theorem graph_component_edge_count (G : SimpleGraph V) :
    (∑ C : G.ConnectedComponent, graphEdgeCount (G.induce C.supp)) = graphEdgeCount G := by
  have hh := Nat.card_congr (componentDartEquiv G)
  simp only [Nat.card_sigma, graph_dart_count, ← Finset.mul_sum] at hh
  omega

theorem graph_excess_euler (G : SimpleGraph V) :
    graphExcess G + Nat.card V = graphEdgeCount G + Nat.card G.ConnectedComponent := by
  have hs := Finset.sum_congr rfl (fun C (_ : C ∈ (Finset.univ : Finset G.ConnectedComponent)) =>
    connected_graph_excess_euler (G.induce C.supp) C.connected_induce_supp)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, Nat.cast_id, ← Nat.card_eq_fintype_card] at hs
  rw [graph_component_vertex_count G, graph_component_edge_count G] at hs
  have hguard : Nat.card V ≤ graphEdgeCount G + Nat.card G.ConnectedComponent := by omega
  have he : G.edgeFinset.card = graphEdgeCount G := by
    simp only [graphEdgeCount, Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
  simpa only [graphExcess, he, ← Nat.card_eq_fintype_card] using Nat.sub_add_cancel hguard

theorem graphExcess_eq_sum_components (G : SimpleGraph V) :
    graphExcess G = ∑ C : G.ConnectedComponent, graphExcess (G.induce C.supp) := by
  have hs := Finset.sum_congr rfl (fun C (_ : C ∈ (Finset.univ : Finset G.ConnectedComponent)) =>
    connected_graph_excess_euler (G.induce C.supp) C.connected_induce_supp)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, Nat.cast_id, ← Nat.card_eq_fintype_card] at hs
  rw [graph_component_vertex_count G, graph_component_edge_count G] at hs
  have hh := graph_excess_euler G
  omega

end LocalLaw
