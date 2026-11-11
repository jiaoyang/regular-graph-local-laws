import LocalLaw.FullEndpointMasks

/-! # Literal signed adjacency sum for all accepted full switchings

Interior endpoints may coincide. Disjoint edge footprints still make the
finite signed sum exact, including every retained-to-exterior update.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance fullSwitchIndicatorDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type}

theorem SwitchingQuad.admissible_indicator_difference (q : SwitchingQuad V) (G : SimpleGraph V)
    (h : q.Admissible G) (x y : V) :
    (if (q.apply G).Adj x y then (1 : ℂ) else 0) - (if G.Adj x y then 1 else 0) =
      (if (switchingAdded q.a q.b q.c q.d).Adj x y then 1 else 0) -
      (if (switchingRemoved q.a q.b q.c q.d).Adj x y then 1 else 0) := by
  have hr : (switchingRemoved q.a q.b q.c q.d).Adj x y → G.Adj x y := fun hh => h.removed_le hh
  have ha : (switchingAdded q.a q.b q.c q.d).Adj x y → ¬G.Adj x y := by
    intro hadd hold
    exact (h.added_disjoint.le_bot ⟨hold, hadd⟩ : False)
  simp only [SwitchingQuad.apply, simpleSwitch, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]
  split_ifs <;> simp_all

namespace LabelledResamplingState
variable {T : Set V} {ι : Type} [Fintype ι]

theorem fullResample_indicator_sum (s : LabelledResamplingState V T ι) (selector : ℕ) (x y : V) :
    (if (s.fullResample selector).graph.Adj x y then (1 : ℂ) else 0) -
      (if s.graph.Adj x y then 1 else 0) =
    ∑ i : s.AdmissibleSampleIndex selector,
      ((if ((s.quad i.val).apply s.graph).Adj x y then (1 : ℂ) else 0) -
        (if s.graph.Adj x y then 1 else 0)) := by
  let L := s.selectedQuads selector (Finset.univ : Finset ι).toList
  by_cases hex : ∃ i : s.AdmissibleSampleIndex selector, (s.quad i.val).footprint.Adj x y
  · obtain ⟨i, hi⟩ := hex
    have hother (j : s.AdmissibleSampleIndex selector) (hji : j ≠ i) :
        ¬(s.quad j.val).footprint.Adj x y := by
      intro hj
      have hraw : i.val ≠ j.val := fun he => hji (Subtype.ext he.symm)
      exact ((s.quad_edge_disjoint selector i.val j.val i.property.2 hraw).le_bot ⟨hi, hj⟩ : False)
    have hsingle : (s.fullResample selector).graph.Adj x y ↔ ((s.quad i.val).apply s.graph).Adj x y := by
      rw [s.fullResample_graph_eq_applySwitches selector]
      apply applySwitches_adj_single_footprint L s.graph (s.quad i.val)
        (s.selectedQuads_nodup selector _ (Finset.nodup_toList _))
        ((s.mem_selectedQuads selector _ _).mpr ⟨i.val, by simp, i.property, rfl⟩)
      intro q hq hneq hqfoot
      obtain ⟨j, _, hj, hqj⟩ := (s.mem_selectedQuads selector _ q).mp hq
      subst q
      exact hother ⟨j,hj⟩ (fun h => hneq (congrArg (fun k : s.AdmissibleSampleIndex selector => s.quad k.val) h)) hqfoot
    rw [Finset.sum_eq_single i]
    · rw [hsingle]
    · intro j _ hji
      rw [(s.quad j.val).adj_outside_footprint s.graph (hother j hji), sub_self]
    · intro hi
      exact False.elim (hi (Finset.mem_univ _))
  · have hnone (i : s.AdmissibleSampleIndex selector) : ¬(s.quad i.val).footprint.Adj x y := by
      intro hi
      exact hex ⟨i,hi⟩
    have hagree : (s.fullResample selector).graph.Adj x y ↔ s.graph.Adj x y := by
      rw [s.fullResample_graph_eq_applySwitches selector]
      apply applySwitches_adj_outside_footprints
      intro q hq
      obtain ⟨i, _, hi, hqi⟩ := (s.mem_selectedQuads selector _ q).mp hq
      subst q
      exact hnone ⟨i,hi⟩
    rw [hagree, sub_self]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [(s.quad i.val).adj_outside_footprint s.graph (hnone i), sub_self]

theorem fullResample_signed_edge_sum (s : LabelledResamplingState V T ι)
    (selector : ℕ) (x y : V) :
    (if (s.fullResample selector).graph.Adj x y then (1 : ℂ) else 0) -
      (if s.graph.Adj x y then 1 else 0) =
    ∑ i : s.AdmissibleSampleIndex selector,
      ((if (switchingAdded (s.quad i.val).a (s.quad i.val).b (s.quad i.val).c (s.quad i.val).d).Adj x y then 1 else 0) -
       (if (switchingRemoved (s.quad i.val).a (s.quad i.val).b (s.quad i.val).c (s.quad i.val).d).Adj x y then 1 else 0)) := by
  rw [s.fullResample_indicator_sum selector x y]
  apply Finset.sum_congr rfl
  intro i _
  exact (s.quad i.val).admissible_indicator_difference s.graph
    (sampledSwitching_admissible s.graph T selector s.samples (s.boundary i.val) i.property.1 i.property.2) x y

end LabelledResamplingState
end LocalLaw
