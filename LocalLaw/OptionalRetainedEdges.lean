import LocalLaw.FullQuadRowCharges
import LocalLaw.FullRetainedPrecision
import LocalLaw.EdgeSubgraphModel

/-! # The actual edge graph of independently retained old core mates -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance optionalRetainedEdgesDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 2000000
variable {K I : Type} [Fintype K] [Fintype I] [DecidableEq K] [DecidableEq I]

def optionalRetainedWitness (inner outer : I → Option K) (x y : K) (i : I) : Prop :=
  (inner i = some x ∧ outer i = some y) ∨ (outer i = some x ∧ inner i = some y)

def optionalRetainedGraph (inner outer : I → Option K) : SimpleGraph K where
  Adj x y := x ≠ y ∧ ∃ i, optionalRetainedWitness inner outer x y i
  symm x y h := ⟨Ne.symm h.1, by
    obtain ⟨i,hi⟩ := h.2
    exact ⟨i,hi.elim (fun h => Or.inr ⟨h.2,h.1⟩) (fun h => Or.inl ⟨h.2,h.1⟩)⟩⟩
  loopless x h := h.1 rfl

omit [Fintype K] [Fintype I] [DecidableEq K] [DecidableEq I] in
theorem optionalRetainedWitness_unique (inner outer : I → Option K)
    (houter : ∀ i j k, outer i = some k → outer j = some k → i = j)
    (hdisjoint : ∀ i j k, inner i = some k → outer j ≠ some k)
    (x y : K) (i j : I)
    (hi : optionalRetainedWitness inner outer x y i)
    (hj : optionalRetainedWitness inner outer x y j) : i = j := by
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact houter i j y hi.2 hj.2
  · exact False.elim (hdisjoint i j x hi.1 hj.1)
  · exact False.elim (hdisjoint j i x hj.1 hi.1)
  · exact houter i j x hi.1 hj.1

omit [Fintype K] [DecidableEq I] in
theorem optionalRetainedGraph_indicator (inner outer : I → Option K)
    (houter : ∀ i j k, outer i = some k → outer j = some k → i = j)
    (hdisjoint : ∀ i j k, inner i = some k → outer j ≠ some k) (x y : K) :
    (if (optionalRetainedGraph inner outer).Adj x y then (1 : ℂ) else 0) =
      fullQuadRetainedEdges inner outer 1 x y := by
  unfold fullQuadRetainedEdges
  by_cases hex : ∃ i, optionalRetainedWitness inner outer x y i
  · obtain ⟨i,hi⟩ := hex
    have hxy : x ≠ y := by
      intro he
      subst y
      rcases hi with hi | hi
      · exact hdisjoint i i x hi.1 hi.2
      · exact hdisjoint i i x hi.2 hi.1
    have hadj : (optionalRetainedGraph inner outer).Adj x y := ⟨hxy,i,hi⟩
    rw [if_pos hadj,Finset.sum_eq_single i]
    · rcases hi with hi | hi
      · simp only [hi.1,hi.2,and_self,if_true]
        have hn : ¬(outer i = some x ∧ inner i = some y) := fun h => hdisjoint i i x hi.1 h.1
        simp [hn,hxy,Ne.symm hxy]
      · have hn : ¬(inner i = some x ∧ outer i = some y) := fun h => hdisjoint i i x h.1 hi.1
        simp [hi.1,hi.2,hn,hxy,Ne.symm hxy]
    · intro j _ hji
      have hn : ¬optionalRetainedWitness inner outer x y j := fun hj =>
        hji (optionalRetainedWitness_unique inner outer houter hdisjoint x y j i hj hi)
      have h1 : ¬(inner j = some x ∧ outer j = some y) := fun h => hn (Or.inl h)
      have h2 : ¬(outer j = some x ∧ inner j = some y) := fun h => hn (Or.inr h)
      simp [h1,h2]
    · simp
  · have hnAdj : ¬(optionalRetainedGraph inner outer).Adj x y := fun h => hex h.2
    rw [if_neg hnAdj]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have h1 : ¬(inner i = some x ∧ outer i = some y) := fun h => hex ⟨i,Or.inl h⟩
    have h2 : ¬(outer i = some x ∧ inner i = some y) := fun h => hex ⟨i,Or.inr h⟩
    simp [h1,h2]

omit [Fintype K] [DecidableEq I] in
theorem optionalRetainedGraph_normalizedAdjacency (inner outer : I → Option K)
    (houter : ∀ i j k, outer i = some k → outer j = some k → i = j)
    (hdisjoint : ∀ i j k, inner i = some k → outer j ≠ some k) (d : ℕ) :
    normalizedAdjacency (optionalRetainedGraph inner outer) d =
      fullQuadRetainedEdges inner outer (treeEdgeWeight d) := by
  ext x y
  simp only [normalizedAdjacency,Matrix.smul_apply,smul_eq_mul,SimpleGraph.adjMatrix_apply]
  rw [optionalRetainedGraph_indicator inner outer houter hdisjoint]
  unfold fullQuadRetainedEdges
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [treeEdgeWeight]
  all_goals ring

end LocalLaw
