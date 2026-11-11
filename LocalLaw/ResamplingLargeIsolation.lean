import LocalLaw.RejectedSwitchingCounts
import LocalLaw.ResamplingEdgeAgreement
import LocalLaw.IsolatedSwitchNeighborhood

/-!
# Larger triple-neighborhood invariance for strongly isolated coordinates

The switching selector may use a smaller radius than the isolation radius
of a particular coordinate. Its own outside modifications are internal to
its triple, while every other original switching footprint is farther away.
The actual full schedule therefore preserves its entire larger union-ball
vertex set, with no false independence or metric-invariance assumption.
-/

noncomputable section
set_option maxHeartbeats 1600000
namespace LocalLaw
namespace LabelledResamplingState

local instance resamplingLargeIsolationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V] {T : Set V} {ι : Type*} [Fintype ι]

omit [Fintype V] in
theorem fullResample_tripleBall_of_strong_isolation (s : LabelledResamplingState V T ι)
    (selector h : ℕ) (i : ι) (hJ : s.JTest h i) :
    (s.fullResample selector).tripleBall h i = s.tripleBall h i := by
  have hTriple := s.fullResample_triple selector i
  unfold tripleBall
  rw [hTriple]
  apply Eq.symm
  apply graphSetBall_eq_of_internal_or_distant_changes
  intro x y hnear haway
  let L := s.selectedQuads selector (Finset.univ : Finset ι).toList
  have hout : ∀ q ∈ L, ¬ q.footprint.Adj x.val y.val := by
    intro q hq hfoot
    obtain ⟨j, _, hj, hqj⟩ := (s.mem_selectedQuads selector _ q).mp hq
    have hExt : x ∈ s.triple j ∧ y ∈ s.triple j := by
      have hx := q.footprint_left_mem_support hfoot
      have hy := q.footprint_left_mem_support hfoot.symm
      rw [← hqj] at hx hy
      have hroot : (s.quad j).a ∈ T := sampledSwitching_root_mem s.graph T s.samples (s.boundary j)
      constructor
      · change x.val = (s.quad j).a ∨ x.val ∈ (s.quad j).exterior at hx
        rcases hx with h | h
        · exact False.elim (x.property (h ▸ hroot))
        · exact h
      · change y.val = (s.quad j).a ∨ y.val ∈ (s.quad j).exterior at hy
        rcases hy with h | h
        · exact False.elim (y.property (h ▸ hroot))
        · exact h
    by_cases hji : j = i
    · subst j
      exact haway.elim (fun hx => hx hExt.1) (fun hy => hy hExt.2)
    · have hlabel : s.boundary j ≠ s.boundary i := fun h => hji (s.boundary.injective h)
      rcases hnear with hx | hy
      · obtain ⟨a, ha, hdist⟩ := hx
        exact (not_lt_of_ge hdist) (hJ (s.boundary j) hlabel a ha x hExt.1)
      · obtain ⟨a, ha, hdist⟩ := hy
        exact (not_lt_of_ge hdist) (hJ (s.boundary j) hlabel a ha y hExt.2)
  have hfinal := congrArg (fun G : SimpleGraph V => G.Adj x.val y.val)
    (s.fullResample_graph_eq_applySwitches selector)
  have hlocal := applySwitches_adj_outside_footprints L s.graph hout
  exact (hfinal.to_iff.trans hlocal).symm

def labelledTripleNearIndices (s : LabelledResamplingState V T ι) (h : ℕ)
    (x : {v : V // v ∉ T}) : Finset ι := Finset.univ.filter (fun i => x ∈ s.tripleBall h i)

def strongIsolationFailures (s : LabelledResamplingState V T ι) (h : ℕ) : Finset ι :=
  Finset.univ.filter (fun i => ¬ s.JTest h i)

omit [Fintype V] in
theorem fullResample_labelledTripleNear_count (s : LabelledResamplingState V T ι)
    (selector h : ℕ) (x : {v : V // v ∉ T}) :
    ((s.fullResample selector).labelledTripleNearIndices h x).card ≤
      (s.labelledTripleNearIndices h x).card + (s.strongIsolationFailures h).card := by
  have hsub : (s.fullResample selector).labelledTripleNearIndices h x ⊆
      s.labelledTripleNearIndices h x ∪ s.strongIsolationFailures h := by
    intro i hi
    by_cases hJ : s.JTest h i
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hx := (Finset.mem_filter.mp hi).2
      rwa [s.fullResample_tripleBall_of_strong_isolation selector h i hJ] at hx
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem labelledTripleNear_card_eq (s : LabelledResamplingState V T ι)
    (h : ℕ) (x : {v : V // v ∉ T}) :
    (s.labelledTripleNearIndices h x).card = (tripleNearIndices s.graph T h s.samples x).card := by
  have himage : (s.labelledTripleNearIndices h x).image s.boundary =
      tripleNearIndices s.graph T h s.samples x := by
    ext α
    constructor
    · intro hα
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hα
      obtain ⟨y, hy, hdist⟩ := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hy, by rwa [SimpleGraph.edist_comm]⟩
    · intro hα
      obtain ⟨y, hy, hdist⟩ := (Finset.mem_filter.mp hα).2
      refine Finset.mem_image.mpr ⟨s.boundary.symm α, ?_, s.boundary.apply_symm_apply α⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, y, ?_, ?_⟩
      · simpa only [triple, s.boundary.apply_symm_apply] using hy
      · rwa [SimpleGraph.edist_comm]
  calc
    _ = ((s.labelledTripleNearIndices h x).image s.boundary).card :=
      (Finset.card_image_of_injective _ s.boundary.injective).symm
    _ = _ := congrArg Finset.card himage

theorem strongIsolationFailures_card (s : LabelledResamplingState V T ι)
    (h R : ℕ) (hR : h ≤ R) :
    (s.strongIsolationFailures h).card ≤
      (boundaryOtherTripleIndices s.graph T h s.samples).card +
        (sampledOtherTripleIndices s.graph T R s.samples).card := by
  have hsub : (s.strongIsolationFailures h).image s.boundary ⊆
      boundaryOtherTripleIndices s.graph T h s.samples ∪ sampledOtherTripleIndices s.graph T R s.samples := by
    intro α hα
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hα
    by_contra hnone
    simp only [Finset.mem_union, not_or] at hnone
    have hJ := isolation_of_not_other_triples s.graph T h h R le_rfl hR s.samples (s.boundary i) hnone.1 hnone.2
    exact (Finset.mem_filter.mp hi).2 hJ
  calc
    _ = ((s.strongIsolationFailures h).image s.boundary).card :=
      (Finset.card_image_of_injective _ s.boundary.injective).symm
    _ ≤ (boundaryOtherTripleIndices s.graph T h s.samples ∪ sampledOtherTripleIndices s.graph T R s.samples).card :=
      Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _

/-- The source switched-graph triple occupancy bound, at any larger radius
h≤R. The finite exceptional cost is proved from the actual full schedule. -/
theorem fullResample_tripleNear_count (s : LabelledResamplingState V T ι)
    (selector h R : ℕ) (hR : h ≤ R) (x : {v : V // v ∉ T}) :
    (tripleNearIndices (s.fullResample selector).graph T h (s.fullResample selector).samples x).card ≤
      (tripleNearIndices s.graph T h s.samples x).card +
      (boundaryOtherTripleIndices s.graph T h s.samples).card +
      (sampledOtherTripleIndices s.graph T R s.samples).card := by
  have hnear := s.fullResample_labelledTripleNear_count selector h x
  have hbad := s.strongIsolationFailures_card h R hR
  rw [labelledTripleNear_card_eq, labelledTripleNear_card_eq] at hnear
  omega

end LabelledResamplingState
end LocalLaw
