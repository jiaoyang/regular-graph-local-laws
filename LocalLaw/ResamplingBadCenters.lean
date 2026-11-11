import LocalLaw.LocalResamplingData
import LocalLaw.SharpBallCounting

/-!
# The bad-center part of geometric resampling stability

An edge modification supported on A leaves every induced radius-r ball whose
center is outside the original r-neighborhood of A unchanged. Consequently
new non-tree centers are confined to that neighborhood. The actual guarded
boundary-switching family has at most four affected vertices per accepted
coordinate. This proves the counting part of Proposition 5.12; the two local
excess bounds in that proposition are separate geometric obligations.
-/

noncomputable section
namespace LocalLaw

local instance resamplingBadCentersDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- Incident-edge agreement away from A gives identical balls at every center
farther than r from A, including the induced edges on their boundary. -/
theorem graphBall_tree_iff_of_modification_away (G H : SimpleGraph V) (A : Set V)
    (hagree : ∀ x y, x ∉ A → (G.Adj x y ↔ H.Adj x y))
    (o : V) (r : ℕ) (ho : o ∉ graphSetBall G A r) :
    (graphBall G o r).IsTree ↔ (graphBall H o r).IsTree := by
  have hdisjoint : ∀ x ∈ graphBallVertices G o r, x ∉ A := by
    intro x hx hA
    apply ho
    exact ⟨x, hA, by simpa only [SimpleGraph.edist_comm] using hx⟩
  have hlocal : ∀ x y,
      x ∈ graphSetBall G {o} r ∨ y ∈ graphSetBall G {o} r →
      (G.Adj x y ↔ H.Adj x y) := by
    intro x y hxy
    rw [graphSetBall_singleton] at hxy
    rcases hxy with hx | hy
    · exact hagree x y (hdisjoint x hx)
    · simpa only [SimpleGraph.adj_comm] using hagree y x (hdisjoint y hy)
  have hsets : graphBallVertices G o r = graphBallVertices H o r := by
    simpa only [graphSetBall_singleton] using
      graphSetBall_eq_of_incident_agreement G H {o} r hlocal
  have hgraphs : G.induce (graphBallVertices G o r) = H.induce (graphBallVertices G o r) := by
    ext x y
    exact hagree x.val y.val (hdisjoint x.val x.property)
  unfold graphBall
  rw [← hsets, hgraphs]

/-- Every newly non-tree center lies near an actual modified vertex. -/
theorem nonTreeCenters_subset_of_modification (G H : SimpleGraph V) (A : Set V)
    (hagree : ∀ x y, x ∉ A → (G.Adj x y ↔ H.Adj x y)) (r : ℕ) :
    nonTreeCenters H r ⊆ nonTreeCenters G r ∪ (graphSetBall G A r).toFinset := by
  intro o ho
  by_cases hnear : o ∈ graphSetBall G A r
  · exact Finset.mem_union_right _ (Set.mem_toFinset.mpr hnear)
  · apply Finset.mem_union_left
    rw [nonTreeCenters_membership] at ho ⊢
    exact fun ht => ho ((graphBall_tree_iff_of_modification_away G H A hagree o r hnear).mp ht)

/-- Deterministic bad-center inflation with the sharp exponential base d-1. -/
theorem nonTreeCenters_card_le_of_modification (G H : SimpleGraph V) (A : Set V)
    (hagree : ∀ x y, x ∉ A → (G.Adj x y ↔ H.Adj x y))
    (d r : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, G.degree v ≤ d) :
    (nonTreeCenters H r).card ≤ (nonTreeCenters G r).card +
      Nat.card A * ((d + 1) * (d - 1) ^ r) := by
  calc
    _ ≤ (nonTreeCenters G r ∪ (graphSetBall G A r).toFinset).card :=
      Finset.card_le_card (nonTreeCenters_subset_of_modification G H A hagree r)
    _ ≤ (nonTreeCenters G r).card + (graphSetBall G A r).toFinset.card :=
      Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left (by
      simpa only [Set.toFinset_card, ← Nat.card_eq_fintype_card] using
        graphSetBall_card_sharp G A d r hd hdegree) _

/-- The finite set of all vertices touched by a finite switching schedule. -/
def switchingScheduleVertices : List (SwitchingQuad V) → Finset V
  | [] => ∅
  | q :: L => {q.a, q.b, q.c, q.d} ∪ switchingScheduleVertices L

omit [Fintype V] in
theorem mem_switchingScheduleVertices (L : List (SwitchingQuad V)) (x : V) :
    x ∈ switchingScheduleVertices L ↔ ∃ q ∈ L, x ∈ q.support := by
  induction L with
  | nil => simp [switchingScheduleVertices]
  | cons q L ih =>
      simp only [switchingScheduleVertices, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, List.mem_cons, ih, SwitchingQuad.support,
      Set.mem_insert_iff, Set.mem_singleton_iff]
      aesop

omit [Fintype V] in
theorem switchingScheduleVertices_card (L : List (SwitchingQuad V)) :
    (switchingScheduleVertices L).card ≤ 4 * L.length := by
  induction L with
  | nil => simp [switchingScheduleVertices]
  | cons q L ih =>
    have hfour : ({q.a, q.b, q.c, q.d} : Finset V).card ≤ 4 := by
      calc
        _ ≤ ({q.b, q.c, q.d} : Finset V).card + 1 := Finset.card_insert_le _ _
        _ ≤ (({q.c, q.d} : Finset V).card + 1) + 1 :=
          Nat.add_le_add_right (Finset.card_insert_le _ _) 1
        _ ≤ ((({q.d} : Finset V).card + 1) + 1) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) 1
        _ = 4 := by simp
    have h := (Finset.card_union_le ({q.a, q.b, q.c, q.d} : Finset V)
      (switchingScheduleVertices L)).trans (Nat.add_le_add hfour ih)
    simpa only [switchingScheduleVertices, List.length_cons, Nat.mul_succ, Nat.add_comm] using h

omit [Fintype V] in
/-- Locality is valid for every schedule, regardless of admissibility or
disjointness: away from all four-vertex supports, every adjacency row agrees. -/
theorem applySwitches_adj_away (L : List (SwitchingQuad V)) (G : SimpleGraph V)
    {x y : V} (hx : x ∉ switchingScheduleVertices L) :
    (applySwitches L G).Adj x y ↔ G.Adj x y := by
  induction L generalizing G with
  | nil => rfl
  | cons q L ih =>
    have hout : x ∉ q.support := by
      intro h
      exact hx ((mem_switchingScheduleVertices (q :: L) x).mpr ⟨q, by simp, h⟩)
    have htail : x ∉ switchingScheduleVertices L := by
      intro h
      exact hx (Finset.mem_union_right _ h)
    exact (ih (q.apply G) htail).trans (q.adj_away G hout)

theorem applySwitches_nonTreeCenters_card (L : List (SwitchingQuad V)) (G : SimpleGraph V)
    (d r : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, G.degree v ≤ d) :
    (nonTreeCenters (applySwitches L G) r).card ≤ (nonTreeCenters G r).card +
      4 * L.length * ((d + 1) * (d - 1) ^ r) := by
  apply (nonTreeCenters_card_le_of_modification G (applySwitches L G)
    (switchingScheduleVertices L) (fun x y hx => (applySwitches_adj_away L G hx).symm)
    d r hd hdegree).trans
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_right
  have hcard : Nat.card (switchingScheduleVertices L : Set V) =
      (switchingScheduleVertices L).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_of_subtype (switchingScheduleVertices L) (by intro x; rfl)
  rw [hcard]
  exact switchingScheduleVertices_card L

/-- Actual accepted boundary switching creates at most the sharp ball volume
times four times the number of accepted coordinates many new bad centers. -/
theorem localResampledGraph_nonTreeCenters_card (G : SimpleGraph V) (T : Set V)
    (radius : ℕ) (S : LocalSamplingFiber G T) (d R : ℕ)
    (hd : 3 ≤ d) (hdegree : ∀ v, G.degree v ≤ d) :
    (nonTreeCenters (localResampledGraph G T radius S) R).card ≤
      (nonTreeCenters G R).card + 4 * (acceptedResamplingIndices G T radius S).card *
        ((d + 1) * (d - 1) ^ R) := by
  simpa only [localResampledGraph, sampledSwitchingFamily, List.length_map,
    Finset.length_toList] using applySwitches_nonTreeCenters_card
      (sampledSwitchingFamily G T S (acceptedResamplingIndices G T radius S)) G d R hd hdegree

theorem localResampledGraph_badCount_twice (G : SimpleGraph V) (T : Set V)
    (radius : ℕ) (S : LocalSamplingFiber G T) (d R badCount : ℕ)
    (hd : 3 ≤ d) (hdegree : ∀ v, G.degree v ≤ d)
    (hbad : (nonTreeCenters G R).card ≤ badCount)
    (hbudget : 4 * Nat.card (BoundaryOrientedEdge G T) *
      ((d + 1) * (d - 1) ^ R) ≤ badCount) :
    (nonTreeCenters (localResampledGraph G T radius S) R).card ≤ 2 * badCount := by
  have haccepted : (acceptedResamplingIndices G T radius S).card ≤
      Nat.card (BoundaryOrientedEdge G T) := by
    simpa only [Nat.card_eq_fintype_card] using
      Finset.card_le_card (Finset.subset_univ (acceptedResamplingIndices G T radius S))
  have h := localResampledGraph_nonTreeCenters_card G T radius S d R hd hdegree
  have hscale := Nat.mul_le_mul_right ((d + 1) * (d - 1) ^ R)
    (Nat.mul_le_mul_left 4 haccepted)
  omega

end LocalLaw
