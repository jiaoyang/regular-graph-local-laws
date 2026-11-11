import LocalLaw.ExcessCutset
import LocalLaw.BicyclicBallWitness

/-!
# Actual Euler-excess bounds for geometric surgery

Connected induced subgraphs and connected injectively embedded subgraphs
cannot have larger excess than their connected ambient graph. Adding an edge
graph K to a connected graph increases excess by at most |E(K)|. Attaching
actual outside tree components by one cut edge preserves excess exactly.
All conclusions are derived from finite edge/component counts and cut Euler
identities, not included in a surgery certificate as final inequalities.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
namespace LocalLaw

local instance graphExcessSurgeryDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {V : Type*} [Fintype V]

theorem graphEdgeCount_mono {G H : SimpleGraph V} (hGH : G ≤ H) :
    graphEdgeCount G ≤ graphEdgeCount H := by
  have h := Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)
  simpa only [graphEdgeCount, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using h

theorem graphEdgeCount_sup_le (G H : SimpleGraph V) :
    graphEdgeCount (G ⊔ H) ≤ graphEdgeCount G + graphEdgeCount H := by
  have h := Finset.card_union_le G.edgeFinset H.edgeFinset
  rw [← SimpleGraph.edgeFinset_sup] at h
  simpa only [graphEdgeCount, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using h

/-- Both connectivity hypotheses are explicit; this elementary edge-count
argument does not silently assume that deletion preserves connectivity. -/
theorem connected_graphExcess_mono {G H : SimpleGraph V} (hGH : G ≤ H)
    (hG : G.Connected) (hH : H.Connected) : graphExcess G ≤ graphExcess H := by
  have h₁ := connected_graph_excess_euler G hG
  have h₂ := connected_graph_excess_euler H hH
  have hE := graphEdgeCount_mono hGH
  omega

/-- The cutset Euler identity proves induced-subgraph excess monotonicity. -/
theorem connected_induce_graphExcess_le (G : SimpleGraph V) (T : Set V)
    (hG : G.Connected) (hT : (G.induce T).Connected) :
    graphExcess (G.induce T) ≤ graphExcess G := by
  have h := connected_cutset_excess_identity G T hG hT
  omega

theorem graphExcess_sup_le_of_connected (G H : SimpleGraph V) (hG : G.Connected) :
    graphExcess (G ⊔ H) ≤ graphExcess G + graphEdgeCount H := by
  have hsup : (G ⊔ H).Connected := hG.mono le_sup_left
  have h₁ := connected_graph_excess_euler G hG
  have h₂ := connected_graph_excess_euler (G ⊔ H) hsup
  have hE := graphEdgeCount_sup_le G H
  omega

variable {W : Type*} [Fintype W]

/-- An actual injective graph homomorphism gives the finite excess bound
for connected subgraphs on a different vertex type. -/
theorem connected_embedding_graphExcess_le (G : SimpleGraph V) (H : SimpleGraph W)
    (hG : G.Connected) (hH : H.Connected) (f : G →g H) (hf : Function.Injective f) :
    graphExcess G ≤ graphExcess H := by
  let A : SimpleGraph V := H.comap f
  have hGA : G ≤ A := fun _ _ h => f.map_rel h
  have hA : A.Connected := hG.mono hGA
  let e : A ≃g H.induce (Set.range f) :=
    { toEquiv := Equiv.ofInjective f hf
      map_rel_iff' := Iff.rfl }
  have hImage : (H.induce (Set.range f)).Connected := e.connected_iff.mp hA
  have h₁ := connected_graphExcess_mono hGA hG hA
  have h₂ := graphExcess_iso e
  have h₃ := connected_induce_graphExcess_le H (Set.range f) hH hImage
  simp only [graphExcess, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
    at h₁ h₂ h₃ ⊢
  omega

/-- Actual nested balls inherit the larger ball's excess budget. -/
theorem graphBallExcess_mono_radius (G : SimpleGraph V) (o : V) {r R : ℕ} (hr : r ≤ R) :
    graphBallExcess G o r ≤ graphBallExcess G o R := by
  let f : graphBall G o r →g graphBall G o R :=
    { toFun := fun v => ⟨v.val, graphBallVertices_mono G o hr v.property⟩
      map_rel' := fun h => h }
  exact connected_embedding_graphExcess_le _ _ (graphBall_connected G o r)
    (graphBall_connected G o R) f (fun _ _ h => Subtype.ext
      (congrArg (fun z : graphBallVertices G o R => z.val) h))

omit [Fintype W] in
/-- Attaching actual tree components by exactly one edge does not create
cycles or spend any additional Euler excess. -/
theorem graphExcess_eq_core_of_tree_attachments (G : SimpleGraph V) (T : Set V)
    (hG : G.Connected) (hT : (G.induce T).Connected)
    (hforest : ∀ C : CutComponent G T, (cutComponentGraph G T C).IsTree)
    (hattach : ∀ C : CutComponent G T, cutMultiplicity G T C ≤ 1) :
    graphExcess G = graphExcess (G.induce T) := by
  have hTnonempty : T.Nonempty := by
    obtain ⟨t⟩ := hT.nonempty
    exact ⟨t.val, t.property⟩
  have hcharge : ∀ C : CutComponent G T, cutExcessCharge G T C = 0 := by
    intro C
    have hpositive := cutMultiplicity_positive G T hG hTnonempty C
    have hone : cutMultiplicity G T C = 1 := by have hh := hattach C; omega
    have hEuler := connected_graph_excess_euler (cutComponentGraph G T C) (hforest C).isConnected
    have hTree := (SimpleGraph.isTree_iff_connected_and_card.mp (hforest C)).2
    have hzero : graphExcess (cutComponentGraph G T C) = 0 := by
      unfold graphEdgeCount at hEuler
      omega
    simp only [cutExcessCharge, hzero, hone, Nat.zero_add, Nat.sub_self]
  have h := connected_cutset_excess_identity G T hG hT
  simpa only [hcharge, Finset.sum_const_zero, Nat.add_zero] using h

end LocalLaw
