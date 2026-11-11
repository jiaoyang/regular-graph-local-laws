import LocalLaw.GoodSampleEvenPatterns
import LocalLaw.SourceFullGeometricEvent
import LocalLaw.GraphExcessSurgery

/-!
# Only finitely many bad added edges can carry large-ball cycles

Good sampled endpoints are excluded from every even pattern of the switched
R/2 ball. Every newly inserted edge touches one such endpoint. Consequently
the mapped even pattern lies in the original graph plus the edges inserted
at the exceptional samples. The latter graph has at most 2(2j+C+t) edges on
the proved full geometric event.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
namespace LocalLaw

local instance badSampleAddedEdgesDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V]

def sampleExceptionalIndices (G : SimpleGraph V) (T : Set V) (R : ℕ)
    (S : LocalSamplingFiber G T) : Finset (BoundaryOrientedEdge G T) :=
  sampledBoundaryHitIndices G T R S ∪
    (sampledOtherTripleIndices G T R S ∪ nonTreeSampledPairIndices G T R S)

def badSampleAddedGraph (G : SimpleGraph V) (T : Set V) (R : ℕ)
    (S : LocalSamplingFiber G T) : SimpleGraph V :=
  (sampleExceptionalIndices G T R S).sup (fun α =>
    switchingAdded (sampledSwitchingQuad G T S α).a (sampledSwitchingQuad G T S α).b
      (sampledSwitchingQuad G T S α).c (sampledSwitchingQuad G T S α).d)

omit [Fintype V] in
theorem graphEdgeCount_edge_le_one (a b : V) : graphEdgeCount (SimpleGraph.edge a b) ≤ 1 := by
  by_cases hab : a = b
  · subst b
    simp [SimpleGraph.edge_self_eq_bot, graphEdgeCount]
  · simp [graphEdgeCount, SimpleGraph.edge_edgeSet_of_ne hab]

theorem graphEdgeCount_switchingAdded_le_two (q : SwitchingQuad V) :
    graphEdgeCount (switchingAdded q.a q.b q.c q.d) ≤ 2 := by
  have h := graphEdgeCount_sup_le (SimpleGraph.edge q.a q.d) (SimpleGraph.edge q.b q.c)
  exact h.trans (by have h₁ := graphEdgeCount_edge_le_one q.a q.d; have h₂ := graphEdgeCount_edge_le_one q.b q.c; omega)

theorem graphEdgeCount_finset_sup_le {I : Type*} (s : Finset I) (F : I → SimpleGraph V) :
    graphEdgeCount (s.sup F) ≤ ∑ i ∈ s, graphEdgeCount (F i) := by
  induction s using Finset.induction_on with
  | empty => simp [graphEdgeCount]
  | @insert i s hi ih =>
    rw [Finset.sup_insert, Finset.sum_insert hi]
    exact (graphEdgeCount_sup_le (F i) (s.sup F)).trans (Nat.add_le_add_left ih _)

theorem badSampleAddedGraph_edgeCount (G : SimpleGraph V) (T : Set V) (R : ℕ)
    (S : LocalSamplingFiber G T) :
    graphEdgeCount (badSampleAddedGraph G T R S) ≤ 2 * (sampleExceptionalIndices G T R S).card := by
  apply (graphEdgeCount_finset_sup_le _ _).trans
  calc
    _ ≤ ∑ _α ∈ sampleExceptionalIndices G T R S, 2 :=
      Finset.sum_le_sum (fun α _ => graphEdgeCount_switchingAdded_le_two (sampledSwitchingQuad G T S α))
    _ = _ := by simp [Nat.mul_comm]

theorem sampleExceptionalIndices_card_of_sourceFullGood (G : SimpleGraph V) (o : V)
    (ell R ω k j C t : ℕ) (S : LocalSamplingFiber G (graphBallVertices G o ell))
    (hgood : SourceFullGeometricGood G o ell R ω k j C t S) :
    (sampleExceptionalIndices G (graphBallVertices G o ell) R S).card ≤ 2 * j + C + t := by
  have h₁ := Finset.card_union_le (sampledBoundaryHitIndices G (graphBallVertices G o ell) R S)
    (sampledOtherTripleIndices G (graphBallVertices G o ell) R S ∪
      nonTreeSampledPairIndices G (graphBallVertices G o ell) R S)
  have h₂ := Finset.card_union_le (sampledOtherTripleIndices G (graphBallVertices G o ell) R S)
    (nonTreeSampledPairIndices G (graphBallVertices G o ell) R S)
  have hmark := hgood.2
  have hother := hgood.1.2.2.1
  have htree := hgood.1.2.2.2
  unfold sampleExceptionalIndices
  omega

omit [Fintype V] in
theorem applySwitches_edge_provenance (L : List (SwitchingQuad V)) (G : SimpleGraph V)
    {x y : V} (h : (applySwitches L G).Adj x y) :
    G.Adj x y ∨ ∃ q ∈ L, (switchingAdded q.a q.b q.c q.d).Adj x y := by
  induction L generalizing G with
  | nil => exact Or.inl h
  | cons q L ih =>
    rcases ih (q.apply G) h with hold | ⟨p, hp, hnew⟩
    · change (G.Adj x y ∧ ¬ (switchingRemoved q.a q.b q.c q.d).Adj x y) ∨
        (switchingAdded q.a q.b q.c q.d).Adj x y at hold
      rcases hold with hold | hnew
      · exact Or.inl hold.1
      · exact Or.inr ⟨q, List.mem_cons_self, hnew⟩
    · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hnew⟩

omit [Fintype V] in
theorem SwitchingQuad.added_touches_sample (q : SwitchingQuad V) {x y : V}
    (h : (switchingAdded q.a q.b q.c q.d).Adj x y) :
    (x = q.c ∨ x = q.d) ∨ (y = q.c ∨ y = q.d) := by
  simp only [switchingAdded, SimpleGraph.sup_adj, SimpleGraph.edge_adj] at h
  aesop

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*} [Fintype ι]

/-- An actual large-ball cyclic pattern uses only original edges and the
bounded exceptional added-edge graph. -/
theorem fullResample_half_ball_even_map_le_old_add_bad (s : LabelledResamplingState V T ι)
    (selector R : ℕ) (center : V)
    (C : EvenEdgeSubgraph (graphBall (s.fullResample selector).graph center (R / 2))) :
    C.val.map (⟨Subtype.val, Subtype.val_injective⟩ :
      (graphBallVertices (s.fullResample selector).graph center (R / 2)) ↪ V) ≤
      s.graph ⊔ badSampleAddedGraph s.graph T R s.samples := by
  let emb : (graphBallVertices (s.fullResample selector).graph center (R / 2)) ↪ V :=
    ⟨Subtype.val, Subtype.val_injective⟩
  intro x y hxy
  obtain ⟨a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj emb C.val x y).mp hxy
  have hcurrent := C.property.1 hab
  have hAdj := congrArg (fun H : SimpleGraph V => H.Adj a.val b.val)
    (s.fullResample_graph_eq_applySwitches selector)
  have hschedule := hAdj.to_iff.mp hcurrent
  rcases applySwitches_edge_provenance _ s.graph hschedule with hold | ⟨q, hq, hnew⟩
  · exact Or.inl hold
  · obtain ⟨i, _, hi, hqi⟩ := (s.mem_selectedQuads selector _ q).mp hq
    subst q
    by_cases hbad : s.boundary i ∈ sampleExceptionalIndices s.graph T R s.samples
    · apply Or.inr
      have hle : switchingAdded (s.quad i).a (s.quad i).b (s.quad i).c (s.quad i).d ≤
          badSampleAddedGraph s.graph T R s.samples := by
        unfold badSampleAddedGraph
        exact Finset.le_sup (f := fun α : BoundaryOrientedEdge s.graph T =>
          switchingAdded (sampledSwitchingQuad s.graph T s.samples α).a
            (sampledSwitchingQuad s.graph T s.samples α).b
            (sampledSwitchingQuad s.graph T s.samples α).c
            (sampledSwitchingQuad s.graph T s.samples α).d) hbad
      exact hle hnew
    · have hgood := hbad
      simp only [sampleExceptionalIndices, Finset.mem_union, not_or] at hgood
      have havoid := s.fullResample_half_ball_even_avoids_good_sample selector R i hi
        hgood.1 hgood.2.1 hgood.2.2 center C
      rcases (s.quad i).added_touches_sample hnew with ha | hb
      · exact False.elim (havoid a ha ((C.val.mem_support).mpr ⟨b, hab⟩))
      · exact False.elim (havoid b hb ((C.val.mem_support).mpr ⟨a, hab.symm⟩))

end LabelledResamplingState
end LocalLaw
