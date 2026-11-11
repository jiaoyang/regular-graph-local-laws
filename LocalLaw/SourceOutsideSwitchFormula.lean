import LocalLaw.IsolatedSwitchNeighborhood
import LocalLaw.SourceEndpointPerturbation

/-!
# The exact bulk outside graph after actual labelled switching

On G(T), the selected original edges b_i-c_i are removed and a_i-b_i are
inserted. Disjoint modified footprints show that each outside edge sees at
most one selected operation. The formula concerns the actual fullResample.
-/

noncomputable section
namespace LocalLaw
local instance sourceOutsideSwitchFormulaDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

theorem SwitchingQuad.outside_apply_adj_iff (q : SwitchingQuad V) (G : SimpleGraph V)
    (T : Set V) (hroot : q.a ∈ T) (x y : (Tᶜ : Set V)) :
    (q.apply G).Adj x.val y.val ↔
      (G.Adj x.val y.val ∧ ¬(SimpleGraph.edge q.c q.d).Adj x.val y.val) ∨
        (SimpleGraph.edge q.b q.c).Adj x.val y.val := by
  have hxa : x.val ≠ q.a := fun h => x.property (h ▸ hroot)
  have hya : y.val ≠ q.a := fun h => y.property (h ▸ hroot)
  have hOldRoot : ¬(SimpleGraph.edge q.a q.b).Adj x.val y.val := by
    simp only [SimpleGraph.edge_adj]
    aesop
  have hNewRoot : ¬(SimpleGraph.edge q.a q.d).Adj x.val y.val := by
    simp only [SimpleGraph.edge_adj]
    aesop
  simp only [SwitchingQuad.apply, simpleSwitch, switchingRemoved, switchingAdded,
    SimpleGraph.sup_adj, SimpleGraph.sdiff_adj, hOldRoot, hNewRoot, false_or]

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*} [Fintype ι]

theorem fullResample_outside_adj_iff (s : LabelledResamplingState V T ι) (selector : ℕ)
    (x y : (Tᶜ : Set V)) :
    (outsideGraph (s.fullResample selector).graph T).Adj x y ↔
      ((outsideGraph s.graph T).Adj x y ∧ ∀ i, s.Eligible selector i →
        ¬(SimpleGraph.edge (s.quad i).c (s.quad i).d).Adj x.val y.val) ∨
      ∃ i, s.Eligible selector i ∧ (SimpleGraph.edge (s.quad i).b (s.quad i).c).Adj x.val y.val := by
  let L := s.selectedQuads selector (Finset.univ : Finset ι).toList
  by_cases hex : ∃ i, s.Eligible selector i ∧ (s.quad i).footprint.Adj x.val y.val
  · obtain ⟨i, hi, hfoot⟩ := hex
    have hother (j : ι) (hj : s.Eligible selector j) (hji : j ≠ i) :
        ¬(s.quad j).footprint.Adj x.val y.val := by
      intro hh
      exact ((s.quad_edge_disjoint selector i j hi.2 (Ne.symm hji)).le_bot ⟨hfoot, hh⟩ : False)
    have hsingle : (outsideGraph (s.fullResample selector).graph T).Adj x y ↔
        ((s.quad i).apply s.graph).Adj x.val y.val := by
      change (s.fullResample selector).graph.Adj x.val y.val ↔ _
      rw [s.fullResample_graph_eq_applySwitches selector]
      apply applySwitches_adj_single_footprint L s.graph (s.quad i)
        (s.selectedQuads_nodup selector _ (Finset.nodup_toList _))
        ((s.mem_selectedQuads selector _ _).mpr ⟨i, by simp, hi, rfl⟩)
      intro q hq hneq hqfoot
      obtain ⟨j, _, hj, hqj⟩ := (s.mem_selectedQuads selector _ q).mp hq
      subst q
      exact hother j hj (fun h => hneq (congrArg s.quad h)) hqfoot
    have hremoved : (∀ j, s.Eligible selector j →
        ¬(SimpleGraph.edge (s.quad j).c (s.quad j).d).Adj x.val y.val) ↔
        ¬(SimpleGraph.edge (s.quad i).c (s.quad i).d).Adj x.val y.val := by
      constructor
      · exact fun h => h i hi
      · intro h j hj hrem
        by_cases hji : j = i
        · exact h (hji ▸ hrem)
        · exact hother j hj hji (Or.inl (Or.inr hrem))
    have hadded : (∃ j, s.Eligible selector j ∧
        (SimpleGraph.edge (s.quad j).b (s.quad j).c).Adj x.val y.val) ↔
        (SimpleGraph.edge (s.quad i).b (s.quad i).c).Adj x.val y.val := by
      constructor
      · rintro ⟨j, hj, hadd⟩
        by_cases hji : j = i
        · exact hji ▸ hadd
        · exact False.elim (hother j hj hji (Or.inr (Or.inr hadd)))
      · exact fun h => ⟨i, hi, h⟩
    rw [hsingle, (s.quad i).outside_apply_adj_iff s.graph T
      (sampledSwitching_root_mem s.graph T s.samples (s.boundary i)) x y]
    exact or_congr (and_congr Iff.rfl hremoved.symm) hadded.symm
  · have hnone : ∀ i, s.Eligible selector i → ¬(s.quad i).footprint.Adj x.val y.val := by
      intro i hi hfoot
      exact hex ⟨i, hi, hfoot⟩
    have hagree : (outsideGraph (s.fullResample selector).graph T).Adj x y ↔
        (outsideGraph s.graph T).Adj x y := by
      change (s.fullResample selector).graph.Adj x.val y.val ↔ s.graph.Adj x.val y.val
      rw [s.fullResample_graph_eq_applySwitches selector]
      apply applySwitches_adj_outside_footprints
      intro q hq
      obtain ⟨i, _, hi, hqi⟩ := (s.mem_selectedQuads selector _ q).mp hq
      subst q
      exact hnone i hi
    have hremoved : ∀ i, s.Eligible selector i →
        ¬(SimpleGraph.edge (s.quad i).c (s.quad i).d).Adj x.val y.val := by
      intro i hi h
      exact hnone i hi (Or.inl (Or.inr h))
    have hadded : ¬∃ i, s.Eligible selector i ∧
        (SimpleGraph.edge (s.quad i).b (s.quad i).c).Adj x.val y.val := by
      rintro ⟨i, hi, h⟩
      exact hnone i hi (Or.inr (Or.inr h))
    rw [hagree]
    constructor
    · exact fun h => Or.inl ⟨h, hremoved⟩
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact False.elim (hadded h)

end LabelledResamplingState
end LocalLaw
