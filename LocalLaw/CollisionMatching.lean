import LocalLaw.SamplingCollision

/-!
# Extracting independent collision pairs

A maximal finite matching covers every nonisolated vertex by the closed
neighborhoods of its endpoints. With degree bound D, at least 2q(D+1)
nonisolated vertices therefore force q disjoint coordinate pairs. Combined
with SamplingCollision, this handles dependent overlapping pair events.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw

local instance collisionMatchingDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {I : Type*} [Fintype I]

def orderedPairSupport (p : I × I) : Finset I := {p.1, p.2}

def OrderedMatching (H : SimpleGraph I) (M : Finset (I × I)) : Prop :=
  (∀ p ∈ M, H.Adj p.1 p.2) ∧
    (M : Set (I × I)).Pairwise (fun p q => Disjoint (orderedPairSupport p) (orderedPairSupport q))

theorem exists_maximal_orderedMatching (H : SimpleGraph I) :
    ∃ M : Finset (I × I), OrderedMatching H M ∧
      ∀ K, OrderedMatching H K → K.card ≤ M.card := by
  let all := (Finset.univ : Finset (Finset (I × I))).filter (OrderedMatching H)
  have hnonempty : all.Nonempty := ⟨∅, by simp [all, OrderedMatching]⟩
  obtain ⟨M, hM, hmax⟩ := all.exists_max_image Finset.card hnonempty
  refine ⟨M, (Finset.mem_filter.mp hM).2, ?_⟩
  intro K hK
  exact hmax K (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hK⟩)

def matchingCover (H : SimpleGraph I) (M : Finset (I × I)) : Finset I :=
  M.biUnion (fun p => (insert p.1 (H.neighborFinset p.1)) ∪
    (insert p.2 (H.neighborFinset p.2)))

/-- The maximality argument is finite and constructive up to selecting a
largest matching; no matching-size lower bound is assumed. -/
theorem support_subset_matchingCover (H : SimpleGraph I) (M : Finset (I × I))
    (hM : OrderedMatching H M)
    (hmax : ∀ K, OrderedMatching H K → K.card ≤ M.card) :
    H.support.toFinset ⊆ matchingCover H M := by
  intro x hx
  by_contra hcover
  obtain ⟨y, hxy⟩ := (H.mem_support).mp (Set.mem_toFinset.mp hx)
  have hout : ∀ p ∈ M, x ≠ p.1 ∧ x ≠ p.2 ∧ y ≠ p.1 ∧ y ≠ p.2 := by
    intro p hp
    have hn : x ∉ (insert p.1 (H.neighborFinset p.1)) ∪
        (insert p.2 (H.neighborFinset p.2)) := by
      intro hh
      exact hcover (Finset.mem_biUnion.mpr ⟨p, hp, hh⟩)
    have hx₁ : x ≠ p.1 := fun h => hn (Finset.mem_union_left _ (Finset.mem_insert.mpr (Or.inl h)))
    have hx₂ : x ≠ p.2 := fun h => hn (Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inl h)))
    refine ⟨hx₁, hx₂, ?_, ?_⟩
    · intro hy
      apply hn
      apply Finset.mem_union_left
      apply Finset.mem_insert_of_mem
      exact (H.mem_neighborFinset p.1 x).mpr (hy ▸ hxy.symm)
    · intro hy
      apply hn
      apply Finset.mem_union_right
      apply Finset.mem_insert_of_mem
      exact (H.mem_neighborFinset p.2 x).mpr (hy ▸ hxy.symm)
  have hdis : ∀ p ∈ M, Disjoint (orderedPairSupport (x, y)) (orderedPairSupport p) := by
    intro p hp
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    have hneq := hout p hp
    simp only [orderedPairSupport, Finset.mem_insert, Finset.mem_singleton] at hz hz'
    aesop
  have hnot : (x, y) ∉ M := by
    intro hp
    exact (hout (x, y) hp).1 rfl
  have hnew : OrderedMatching H (insert (x, y) M) := by
    constructor
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact hxy
      · exact hM.1 p hp
    · intro p hp q hq hpq
      rcases Finset.mem_insert.mp hp with rfl | hp <;>
        rcases Finset.mem_insert.mp hq with rfl | hq
      · exact False.elim (hpq rfl)
      · exact hdis q hq
      · exact (hdis p hp).symm
      · exact hM.2 hp hq hpq
  have hcard := hmax _ hnew
  rw [Finset.card_insert_of_not_mem hnot] at hcard
  omega

theorem matchingCover_card (H : SimpleGraph I) (M : Finset (I × I)) (D : ℕ)
    (hD : ∀ i, H.degree i ≤ D) :
    (matchingCover H M).card ≤ M.card * (2 * (D + 1)) := by
  calc
    _ ≤ ∑ p ∈ M, ((insert p.1 (H.neighborFinset p.1)) ∪
        (insert p.2 (H.neighborFinset p.2))).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ M, 2 * (D + 1) := by
      apply Finset.sum_le_sum
      intro p _
      have h₁ : (insert p.1 (H.neighborFinset p.1)).card ≤ D + 1 := by
        apply (Finset.card_insert_le _ _).trans
        simpa only [SimpleGraph.card_neighborFinset_eq_degree] using Nat.add_le_add_right (hD p.1) 1
      have h₂ : (insert p.2 (H.neighborFinset p.2)).card ≤ D + 1 := by
        apply (Finset.card_insert_le _ _).trans
        simpa only [SimpleGraph.card_neighborFinset_eq_degree] using Nat.add_le_add_right (hD p.2) 1
      exact (Finset.card_union_le _ _).trans (by omega)
    _ = _ := by simp

omit [Fintype I] in
theorem orderedMatching_pair_embedding (H : SimpleGraph I) (M : Finset (I × I))
    (hM : OrderedMatching H M) (q : ℕ) (hq : q ≤ M.card) :
    ∃ e : (Fin q × Bool) ↪ I, ∀ j, H.Adj (e (j, false)) (e (j, true)) := by
  obtain ⟨a⟩ := Function.Embedding.nonempty_of_card_le (α := Fin q) (β := M) (by simpa using hq)
  let f : Fin q × Bool → I := fun p => if p.2 then (a p.1).val.2 else (a p.1).val.1
  have hf : Function.Injective f := by
    rintro ⟨i, b⟩ ⟨j, c⟩ hij
    have hpairs : (a i).val = (a j).val := by
      by_contra hp
      have hd := hM.2 (a i).property (a j).property hp
      apply Finset.disjoint_left.mp hd
      · change f (i, b) ∈ orderedPairSupport (a i).val
        cases b <;> simp [f, orderedPairSupport]
      · rw [hij]
        cases c <;> simp [f, orderedPairSupport]
    have heq : i = j := a.injective (Subtype.ext hpairs)
    subst j
    have hc : b = c := by
      have hn := (hM.1 (a i).val (a i).property).ne
      cases b <;> cases c <;> simp_all [f]
    exact Prod.ext rfl hc
  exact ⟨⟨f, hf⟩, fun j => hM.1 (a j).val (a j).property⟩

/-- Enough active collision indices force q genuinely disjoint pairs. -/
theorem disjoint_collision_pairs_of_support_card (H : SimpleGraph I) (D q : ℕ)
    (hD : ∀ i, H.degree i ≤ D)
    (hcard : 2 * q * (D + 1) ≤ H.support.toFinset.card) :
    ∃ e : (Fin q × Bool) ↪ I, ∀ j, H.Adj (e (j, false)) (e (j, true)) := by
  obtain ⟨M, hM, hmax⟩ := exists_maximal_orderedMatching H
  have hcover := (Finset.card_le_card (support_subset_matchingCover H M hM hmax)).trans
    (matchingCover_card H M D hD)
  have hq : q ≤ M.card := by nlinarith
  exact orderedMatching_pair_embedding H M hM q hq

variable {E : Type*} [Fintype E]

/-- The actual collision graph on sample coordinates; distinct coordinates
are required even when R is reflexive on sample values. -/
def sampleCollisionGraph (R : E → E → Prop) (hR : Symmetric R) (f : I → E) : SimpleGraph I where
  Adj i j := i ≠ j ∧ R (f i) (f j)
  symm := fun _ _ h => ⟨h.1.symm, hR h.2⟩
  loopless := fun _ h => h.1 rfl

/-- The pair-event estimate on the explicit bounded-degree part of sample
space. The degree restriction is a pointwise event, not a probability input. -/
theorem uniform_collision_support_tail_on_degree [Nonempty E]
    (R : E → E → Prop) (hR : Symmetric R) (b D q : ℕ)
    (hb : ∀ x, Nat.card {y : E // R x y} ≤ b) :
    eventMass (finiteUniformWeight (I → E)) (fun f =>
      (∀ i, (sampleCollisionGraph R hR f).degree i ≤ D) ∧
        2 * q * (D + 1) ≤ (sampleCollisionGraph R hR f).support.toFinset.card) ≤
      (((Fintype.card I : ℝ) ^ 2) * ((b : ℝ) / Fintype.card E)) ^ q := by
  apply (eventMass_mono (finiteUniformWeight (I → E)) finiteUniformWeight_nonneg ?_).trans
    (uniform_exists_disjointPairConstraint_tail R b q hb)
  intro f hf
  obtain ⟨e, he⟩ := disjoint_collision_pairs_of_support_card
    (sampleCollisionGraph R hR f) D q hf.1 hf.2
  exact ⟨e, fun j => (he j).2⟩

end LocalLaw
