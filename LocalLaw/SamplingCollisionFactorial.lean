import LocalLaw.CollisionMatching

/-!
# Factorial improvement for independent disjoint-pair collisions

Overlapping collision events are dependent. A union over UNORDERED finite
sets of disjoint coordinate pairs retains the binomial/factorial saving,
instead of counting every ordering of the same matching. This handles a
bounded (rather than vanishing) expected number of pair collisions.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance samplingCollisionFactorialDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section PairEnumeration
variable {I : Type*}

/-- Enumerate actual pairs of a matching, retaining membership information. -/
theorem orderedMatching_pair_embedding_mem (H : SimpleGraph I) (M : Finset (I × I))
    (hM : OrderedMatching H M) (q : ℕ) (hq : q ≤ M.card) :
    ∃ e : (Fin q × Bool) ↪ I, ∀ j, (e (j, false), e (j, true)) ∈ M := by
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
  exact ⟨⟨f, hf⟩, fun j => (a j).property⟩

end PairEnumeration

section Probability
variable {I E : Type*} [Fintype I] [Fintype E] [Nonempty E]

def PairSetConstraint (R : E → E → Prop) (M : Finset (I × I)) (f : I → E) : Prop :=
  OrderedMatching (⊤ : SimpleGraph I) M ∧ ∀ p ∈ M, R (f p.1) (f p.2)

/-- The actual probability of a prescribed unordered matching. -/
theorem uniform_pairSetConstraint_probability (R : E → E → Prop) (M : Finset (I × I))
    (q : ℕ) (hcard : M.card = q) (p : ℝ) (hp : 0 ≤ p)
    (hpair : (Nat.card {x : E × E // R x.1 x.2} : ℝ) / (Fintype.card E : ℝ) ^ 2 ≤ p) :
    eventMass (finiteUniformWeight (I → E)) (PairSetConstraint R M) ≤ p ^ q := by
  by_cases hM : OrderedMatching (⊤ : SimpleGraph I) M
  · obtain ⟨e, he⟩ := orderedMatching_pair_embedding_mem (⊤ : SimpleGraph I) M hM q hcard.ge
    apply (eventMass_mono (finiteUniformWeight (I → E)) finiteUniformWeight_nonneg ?_).trans
      ((uniform_disjointPairConstraint_probability R e).trans (pow_le_pow_left₀ (by positivity) hpair _))
    intro f hf j
    exact hf.2 _ (he j)
  · have hz : eventMass (finiteUniformWeight (I → E)) (PairSetConstraint R M) = 0 := by
      simp only [eventMass, PairSetConstraint, hM, false_and, ↓reduceIte, Finset.sum_const_zero]
    rw [hz]
    exact pow_nonneg hp _

/-- Union over finite q-element sets of pairs, preserving q! savings. -/
theorem uniform_exists_pairSetConstraint_tail (R : E → E → Prop) (q : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hpair : (Nat.card {x : E × E // R x.1 x.2} : ℝ) / (Fintype.card E : ℝ) ^ 2 ≤ p) :
    eventMass (finiteUniformWeight (I → E)) (fun f =>
      ∃ M ∈ (Finset.univ : Finset (I × I)).powersetCard q, PairSetConstraint R M f) ≤
        (((Fintype.card I) ^ 2).choose q : ℝ) * p ^ q := by
  have h := eventMass_exists_finset_le ((Finset.univ : Finset (I × I)).powersetCard q)
    (finiteUniformWeight (I → E)) finiteUniformWeight_nonneg (PairSetConstraint R)
  apply h.trans
  calc
    _ ≤ ∑ _M ∈ (Finset.univ : Finset (I × I)).powersetCard q, p ^ q := by
      apply Finset.sum_le_sum
      intro M hM
      exact uniform_pairSetConstraint_probability R M q (Finset.mem_powersetCard.mp hM).2 p hp hpair
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_prod, ← pow_two]

/-- The factorial denominator is retained even when m^2*p is only bounded. -/
theorem uniform_exists_pairSetConstraint_factorial (R : E → E → Prop) (q : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hpair : (Nat.card {x : E × E // R x.1 x.2} : ℝ) / (Fintype.card E : ℝ) ^ 2 ≤ p) :
    eventMass (finiteUniformWeight (I → E)) (fun f =>
      ∃ M ∈ (Finset.univ : Finset (I × I)).powersetCard q, PairSetConstraint R M f) ≤
        (((Fintype.card I : ℝ) ^ 2) * p) ^ q / (Nat.factorial q : ℝ) := by
  apply (uniform_exists_pairSetConstraint_tail R q p hp hpair).trans
  have hchoose := mul_le_mul_of_nonneg_right
    (Nat.choose_le_pow_div (α := ℝ) q ((Fintype.card I) ^ 2)) (pow_nonneg hp q)
  apply hchoose.trans_eq
  push_cast
  rw [mul_pow]
  ring

/-- Bounded-degree active collision support forces the actual unordered
matching event, without assuming independence of overlapping pair events. -/
theorem uniform_collision_support_factorial_tail (R : E → E → Prop) (hR : Symmetric R)
    (D q : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hpair : (Nat.card {x : E × E // R x.1 x.2} : ℝ) / (Fintype.card E : ℝ) ^ 2 ≤ p) :
    eventMass (finiteUniformWeight (I → E)) (fun f =>
      (∀ i, (sampleCollisionGraph R hR f).degree i ≤ D) ∧
        2 * q * (D + 1) ≤ (sampleCollisionGraph R hR f).support.toFinset.card) ≤
        (((Fintype.card I : ℝ) ^ 2) * p) ^ q / (Nat.factorial q : ℝ) := by
  apply (eventMass_mono (finiteUniformWeight (I → E)) finiteUniformWeight_nonneg ?_).trans
    (uniform_exists_pairSetConstraint_factorial R q p hp hpair)
  intro f hf
  let H := sampleCollisionGraph R hR f
  obtain ⟨M, hM, hmax⟩ := exists_maximal_orderedMatching H
  have hcover := (Finset.card_le_card (support_subset_matchingCover H M hM hmax)).trans
    (matchingCover_card H M D hf.1)
  have hq : q ≤ M.card := by have hh := hf.2; nlinarith
  obtain ⟨K, hKM, hKcard⟩ := Finset.exists_subset_card_eq hq
  refine ⟨K, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hKcard⟩, ?_, ?_⟩
  · constructor
    · intro a ha
      exact (hM.1 a (hKM ha)).ne
    · intro a ha b hb hab
      exact hM.2 (hKM ha) (hKM hb) hab
  · intro a ha
    exact (hM.1 a (hKM ha)).2

end Probability
end LocalLaw
