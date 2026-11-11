import LocalLaw.FactorialLogTail

/-!
# Isolated sampled pairs from actual independent finite sampling

A sampled pair is good when it is unrelated to every fixed old point and to
all other sampled pairs. The proof counts fixed-point hits and unordered
matching collisions, retaining their factorial savings. Per-point occupancy
controls the collision graph degree; overlapping pair events are never
assumed independent.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance correlationIsolationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Definitions
variable {I E X : Type*}

def endpointRelated (R : X → X → Prop) (first second : E → X) (x : X) (e : E) : Prop :=
  R x (first e) ∨ R x (second e)

def pairEndpointRelated (R : X → X → Prop) (first second : E → X) (e f : E) : Prop :=
  endpointRelated R first second (first e) f ∨ endpointRelated R first second (second e) f

theorem pairEndpointRelated_symmetric (R : X → X → Prop) (hR : Symmetric R) (first second : E → X) :
    Symmetric (pairEndpointRelated R first second) := by
  intro e f h
  rcases h with (h | h) | (h | h)
  · exact Or.inl (Or.inl (hR h))
  · exact Or.inr (Or.inl (hR h))
  · exact Or.inl (Or.inr (hR h))
  · exact Or.inr (Or.inr (hR h))

end Definitions

section Finite
variable {I E X : Type*} [Fintype I] [Fintype E] [Nonempty E]

def relatedSampleIndices (R : X → X → Prop) (first second : E → X) (x : X) (f : I → E) : Finset I :=
  Finset.univ.filter (fun a => endpointRelated R first second x (f a))

def oldPointHitSet (R : X → X → Prop) (first second : E → X) (old : I → X) : Finset E :=
  Finset.univ.biUnion (fun a => Finset.univ.filter (endpointRelated R first second (old a)))

omit [Nonempty E] in
/-- Exact uniform product disintegration, proved by finite sums. -/
theorem uniform_relation_pair_fraction (R : E → E → Prop) :
    (Nat.card {x : E × E // R x.1 x.2} : ℝ) / (Fintype.card E : ℝ) ^ 2 =
      ∑ x : E, finiteUniformWeight E x * eventMass (finiteUniformWeight E) (R x) := by
  have hcard := uniform_eventMass_cardinality (fun x : E × E => R x.1 x.2)
  have hmass : eventMass (finiteUniformWeight (E × E)) (fun x => R x.1 x.2) =
      ∑ x : E, finiteUniformWeight E x * eventMass (finiteUniformWeight E) (R x) := by
    simp only [eventMass, finiteUniformWeight, Fintype.card_prod, Nat.cast_mul,
      Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    by_cases h : R x y <;> simp [h]
  simpa only [Fintype.card_prod, Nat.cast_mul, pow_two] using hcard.symm.trans hmass

/-- Two endpoint rare events bound the actual two-draw relation probability. -/
theorem pairEndpointRelated_fraction_bound (R : X → X → Prop) (first second : E → X)
    (p : ℝ) (hprob : ∀ x, eventMass (finiteUniformWeight E) (endpointRelated R first second x) ≤ p) :
    (Nat.card {x : E × E // pairEndpointRelated R first second x.1 x.2} : ℝ) /
      (Fintype.card E : ℝ) ^ 2 ≤ 2 * p := by
  rw [uniform_relation_pair_fraction]
  calc
    _ ≤ ∑ x : E, finiteUniformWeight E x * (2 * p) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (finiteUniformWeight_nonneg x)
      exact (eventMass_union_le (finiteUniformWeight E) finiteUniformWeight_nonneg _ _).trans
        (by have h1 := hprob (first x); have h2 := hprob (second x); linarith)
    _ = _ := by rw [← Finset.sum_mul, finiteUniformWeight_total, one_mul]

omit [Nonempty E] in
/-- The fixed old points are a finite union of actual one-draw rare events. -/
theorem oldPointHitSet_probability (R : X → X → Prop) (first second : E → X) (old : I → X)
    (p : ℝ) (hprob : ∀ x, eventMass (finiteUniformWeight E) (endpointRelated R first second x) ≤ p) :
    uniformBadProbability (oldPointHitSet R first second old) ≤ (Fintype.card I : ℝ) * p := by
  rw [uniformBadProbability_eq_eventMass]
  have hh := eventMass_exists_finset_le (Finset.univ : Finset I) (finiteUniformWeight E)
    finiteUniformWeight_nonneg (fun a e => endpointRelated R first second (old a) e)
  have heq : (fun e => e ∈ oldPointHitSet R first second old) =
      (fun e => ∃ a ∈ (Finset.univ : Finset I), endpointRelated R first second (old a) e) := by
    funext e
    simp only [oldPointHitSet, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [heq]
  apply hh.trans
  calc
    _ ≤ ∑ _a : I, p := Finset.sum_le_sum (fun a _ => hprob (old a))
    _ = _ := by simp

/-- Actual fixed-point hit tail including the factorial denominator. -/
theorem uniform_oldPointHit_factorial_tail (R : X → X → Prop) (first second : E → X) (old : I → X)
    (q : ℕ) (p : ℝ) (_hp : 0 ≤ p)
    (hprob : ∀ x, eventMass (finiteUniformWeight E) (endpointRelated R first second x) ≤ p) :
    eventMass (finiteUniformWeight (I → E)) (fun f =>
      q ≤ (badSampleIndices (oldPointHitSet R first second old) f).card) ≤
      (((Fintype.card I : ℝ) ^ 2) * p) ^ q / (Nat.factorial q : ℝ) := by
  letI : MeasurableSpace E := ⊤
  have htail := uniform_bad_sample_eventMass_tail (I := I) (oldPointHitSet R first second old) q
  have hBad := uniformBadProbability_nonnegative (oldPointHitSet R first second old)
  have hprobOld := oldPointHitSet_probability (I := I) R first second old p hprob
  have hchoose := Nat.choose_le_pow_div (α := ℝ) q (Fintype.card I)
  have hmean := mul_le_mul_of_nonneg_left hprobOld (Nat.cast_nonneg (α := ℝ) (Fintype.card I))
  apply htail.trans
  calc
    _ ≤ (((Fintype.card I : ℝ) ^ q) / (Nat.factorial q : ℝ)) *
        uniformBadProbability (oldPointHitSet R first second old) ^ q :=
      mul_le_mul_of_nonneg_right hchoose (by positivity)
    _ = (((Fintype.card I : ℝ) * uniformBadProbability (oldPointHitSet R first second old)) ^ q) /
        (Nat.factorial q : ℝ) := by rw [mul_pow]; ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      exact hmean.trans_eq (by ring)

omit [Fintype E] [Nonempty E] in
/-- Per-point occupancy bounds the actual sample-pair collision degree. -/
theorem pairEndpointCollision_degree (R : X → X → Prop) (hR : Symmetric R)
    (first second : E → X) (f : I → E) (k : ℕ)
    (hcount : ∀ x, (relatedSampleIndices R first second x f).card ≤ k) (a : I) :
    (sampleCollisionGraph (pairEndpointRelated R first second)
      (pairEndpointRelated_symmetric R hR first second) f).degree a ≤ 2 * k := by
  let H := sampleCollisionGraph (pairEndpointRelated R first second)
    (pairEndpointRelated_symmetric R hR first second) f
  have hsub : H.neighborFinset a ⊆ relatedSampleIndices R first second (first (f a)) f ∪
      relatedSampleIndices R first second (second (f a)) f := by
    intro b hb
    have hh := ((H.mem_neighborFinset a b).mp hb).2
    simpa only [relatedSampleIndices, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, pairEndpointRelated] using hh
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by
    have h1 := hcount (first (f a)); have h2 := hcount (second (f a)); omega))

/-- Pair-isolation failures are bounded by the already controlled per-point
occupancy event plus two genuine factorial tails. -/
theorem uniform_correlation_isolation_failure (R : X → X → Prop) (hR : Symmetric R)
    (first second : E → X) (old : I → X) (q : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hprob : ∀ x, eventMass (finiteUniformWeight E) (endpointRelated R first second x) ≤ p) :
    eventMass (finiteUniformWeight (I → E)) (fun f =>
      q ≤ (badSampleIndices (oldPointHitSet R first second old) f).card ∨
        2 * q * (2 * q + 1) ≤ (sampleCollisionGraph (pairEndpointRelated R first second)
          (pairEndpointRelated_symmetric R hR first second) f).support.toFinset.card) ≤
      eventMass (finiteUniformWeight (I → E)) (fun f =>
        ∃ x, q ≤ (relatedSampleIndices R first second x f).card) +
      (((Fintype.card I : ℝ) ^ 2) * p) ^ q / (Nat.factorial q : ℝ) +
      (((Fintype.card I : ℝ) ^ 2) * (2 * p)) ^ q / (Nat.factorial q : ℝ) := by
  let pairR := pairEndpointRelated R first second
  let pairSymm := pairEndpointRelated_symmetric R hR first second
  let occupancyBad := fun f : I → E => ∃ x, q ≤ (relatedSampleIndices R first second x f).card
  let oldBad := fun f : I → E => q ≤ (badSampleIndices (oldPointHitSet R first second old) f).card
  let collisionBad := fun f : I → E =>
    (∀ i, (sampleCollisionGraph pairR pairSymm f).degree i ≤ 2 * q) ∧
      2 * q * (2 * q + 1) ≤ (sampleCollisionGraph pairR pairSymm f).support.toFinset.card
  have hcover : ∀ f : I → E,
      (oldBad f ∨ 2 * q * (2 * q + 1) ≤ (sampleCollisionGraph pairR pairSymm f).support.toFinset.card) →
      occupancyBad f ∨ oldBad f ∨ collisionBad f := by
    intro f hf
    by_cases hocc : occupancyBad f
    · exact Or.inl hocc
    · right
      rcases hf with h | h
      · exact Or.inl h
      · right
        refine ⟨?_, h⟩
        intro i
        exact pairEndpointCollision_degree R hR first second f q (fun x => by
          have hx : ¬q ≤ (relatedSampleIndices R first second x f).card := fun hh => hocc ⟨x, hh⟩
          omega) i
  have hmono := eventMass_mono (finiteUniformWeight (I → E)) finiteUniformWeight_nonneg hcover
  have hunion := eventMass_union_le (finiteUniformWeight (I → E)) finiteUniformWeight_nonneg
    occupancyBad (fun f => oldBad f ∨ collisionBad f)
  have hunion' := eventMass_union_le (finiteUniformWeight (I → E)) finiteUniformWeight_nonneg oldBad collisionBad
  have hold := uniform_oldPointHit_factorial_tail R first second old q p hp hprob
  have hpair := uniform_collision_support_factorial_tail (I := I) pairR pairSymm (2 * q) q (2 * p)
    (by positivity) (pairEndpointRelated_fraction_bound R first second p hprob)
  exact hmono.trans (hunion.trans (by linarith only [hunion', hold, hpair]))

end Finite
end LocalLaw
