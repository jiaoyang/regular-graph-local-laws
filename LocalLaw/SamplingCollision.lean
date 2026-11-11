import LocalLaw.ResamplingSamplingGeometry

/-!
# Dependent pair-collision events under independent finite sampling

Collision events sharing a coordinate are generally dependent. Prescribed
disjoint coordinate pairs, however, admit a direct finite counting proof of
the product bound. This module supplies that elementary ingredient without
assuming independence of overlapping pair events.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw

local instance samplingCollisionDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {I E : Type*} [Fintype I] [Fintype E]

/-- All q prescribed pairs satisfy R; the embedding forces 2q distinct
coordinate labels, which is the essential independence condition. -/
def DisjointPairConstraint (R : E → E → Prop) {q : ℕ}
    (e : (Fin q × Bool) ↪ I) (f : I → E) : Prop :=
  ∀ j, R (f (e (j, false))) (f (e (j, true)))

/-- Encode favorable functions by q related sample pairs and their values
on the unused coordinates. This is an actual injective finite counting map. -/
def disjointPairEncoding (R : E → E → Prop) {q : ℕ} (e : (Fin q × Bool) ↪ I) :
    {f : I → E // DisjointPairConstraint R e f} →
      (Fin q → {p : E × E // R p.1 p.2}) × ({i : I // i ∉ Set.range e} → E) :=
  fun f => (fun j => ⟨(f.val (e (j, false)), f.val (e (j, true))), f.property j⟩,
    fun i => f.val i.val)

omit [Fintype I] [Fintype E] in
theorem disjointPairEncoding_injective (R : E → E → Prop) {q : ℕ}
    (e : (Fin q × Bool) ↪ I) : Function.Injective (disjointPairEncoding R e) := by
  intro f g h
  apply Subtype.ext
  funext i
  by_cases hi : i ∈ Set.range e
  · obtain ⟨⟨j, b⟩, rfl⟩ := hi
    have hp := congrFun (congrArg Prod.fst h) j
    have hv := congrArg Subtype.val hp
    cases b
    · exact congrArg Prod.fst hv
    · exact congrArg Prod.snd hv
  · exact congrFun (congrArg Prod.snd h) ⟨i, hi⟩

theorem disjointPair_unused_card {q : ℕ} (e : (Fin q × Bool) ↪ I) :
    Nat.card {i : I // i ∉ Set.range e} + 2 * q = Fintype.card I := by
  have hcard : Fintype.card (Set.range e) = 2 * q := by
    rw [Fintype.card_range e]
    simp [Nat.mul_comm]
  have hle : 2 * q ≤ Fintype.card I := by
    rw [← hcard]
    exact Fintype.card_subtype_le _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, hcard]
  omega

/-- The exact favorable-count upper bound before normalizing the uniform
law. No measure or independence axiom occurs in its proof. -/
theorem disjointPairConstraint_card (R : E → E → Prop) {q : ℕ}
    (e : (Fin q × Bool) ↪ I) :
    Nat.card {f : I → E // DisjointPairConstraint R e f} ≤
      (Nat.card {p : E × E // R p.1 p.2}) ^ q *
        (Fintype.card E) ^ (Nat.card {i : I // i ∉ Set.range e}) := by
  have h := Nat.card_le_card_of_injective (disjointPairEncoding R e)
    (disjointPairEncoding_injective R e)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin] using h

/-- The genuine disjoint-pair product probability. -/
theorem uniform_disjointPairConstraint_probability [Nonempty E]
    (R : E → E → Prop) {q : ℕ} (e : (Fin q × Bool) ↪ I) :
    eventMass (finiteUniformWeight (I → E)) (DisjointPairConstraint R e) ≤
      ((Nat.card {p : E × E // R p.1 p.2} : ℝ) / (Fintype.card E : ℝ) ^ 2) ^ q := by
  rw [uniform_eventMass_cardinality, Fintype.card_fun, Nat.cast_pow]
  have hE : (0 : ℝ) < Fintype.card E := Nat.cast_pos.mpr Fintype.card_pos
  have hsize := disjointPair_unused_card e
  have hpow : (Fintype.card E : ℝ) ^ Fintype.card I =
      (Fintype.card E : ℝ) ^ Nat.card {i : I // i ∉ Set.range e} *
        ((Fintype.card E : ℝ) ^ 2) ^ q := by
    rw [← hsize, pow_add, pow_mul]
  have hcount : (Nat.card {f : I → E // DisjointPairConstraint R e f} : ℝ) ≤
      (Nat.card {p : E × E // R p.1 p.2} : ℝ) ^ q *
        (Fintype.card E : ℝ) ^ Nat.card {i : I // i ∉ Set.range e} := by
    exact_mod_cast disjointPairConstraint_card R e
  apply (div_le_div_of_nonneg_right hcount (pow_nonneg hE.le _)).trans
  rw [hpow, div_pow]
  have hc : (Fintype.card E : ℝ) ^ Nat.card {i : I // i ∉ Set.range e} ≠ 0 :=
    pow_ne_zero _ (ne_of_gt hE)
  apply le_of_eq
  field_simp [hc]
  ring

/-- A uniform row-cardinality bound controls the two-sample collision
fraction, again by an explicit finite injection into endpoint fibers. -/
theorem relation_pair_card_bound (R : E → E → Prop) (b : ℕ)
    (hb : ∀ x, Nat.card {y : E // R x y} ≤ b) :
    Nat.card {p : E × E // R p.1 p.2} ≤ Fintype.card E * b := by
  let enc : {p : E × E // R p.1 p.2} → Σ x : E, {y : E // R x y} :=
    fun p => ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
  have hinj : Function.Injective enc := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun z : Σ x : E, {y : E // R x y} => (z.1, z.2.val)) h
  calc
    _ ≤ Nat.card (Σ x : E, {y : E // R x y}) := Nat.card_le_card_of_injective enc hinj
    _ = ∑ x : E, Nat.card {y : E // R x y} := Nat.card_sigma
    _ ≤ ∑ _x : E, b := Finset.sum_le_sum (fun x _ => hb x)
    _ = _ := by simp

theorem uniform_disjointPairConstraint_row_bound [Nonempty E]
    (R : E → E → Prop) (b : ℕ) (hb : ∀ x, Nat.card {y : E // R x y} ≤ b)
    {q : ℕ} (e : (Fin q × Bool) ↪ I) :
    eventMass (finiteUniformWeight (I → E)) (DisjointPairConstraint R e) ≤
      ((b : ℝ) / Fintype.card E) ^ q := by
  apply (uniform_disjointPairConstraint_probability R e).trans
  apply pow_le_pow_left₀ (by positivity)
  have hE : (0 : ℝ) < Fintype.card E := Nat.cast_pos.mpr Fintype.card_pos
  have hc : (Nat.card {p : E × E // R p.1 p.2} : ℝ) ≤ (Fintype.card E : ℝ) * b := by
    exact_mod_cast relation_pair_card_bound R b hb
  apply (div_le_div_of_nonneg_right hc (sq_nonneg _)).trans_eq
  field_simp
  ring

/-- Union over every way to choose q disjoint coordinate pairs. The number
of embeddings is bounded by m^(2q), giving the explicit (m²p)^q loss. -/
theorem uniform_exists_disjointPairConstraint_tail [Nonempty E]
    (R : E → E → Prop) (b q : ℕ) (hb : ∀ x, Nat.card {y : E // R x y} ≤ b) :
    eventMass (finiteUniformWeight (I → E))
      (fun f => ∃ e : (Fin q × Bool) ↪ I, DisjointPairConstraint R e f) ≤
      (((Fintype.card I : ℝ) ^ 2) * ((b : ℝ) / Fintype.card E)) ^ q := by
  have h := eventMass_exists_finset_le (Finset.univ : Finset ((Fin q × Bool) ↪ I))
    (finiteUniformWeight (I → E)) finiteUniformWeight_nonneg
    (fun e f => DisjointPairConstraint R e f)
  simp only [Finset.mem_univ, true_and] at h
  apply h.trans
  have hcount : (Fintype.card ((Fin q × Bool) ↪ I) : ℝ) ≤ (Fintype.card I : ℝ) ^ (2 * q) := by
    have hle := Fintype.card_le_of_injective (fun e : (Fin q × Bool) ↪ I => (e : (Fin q × Bool) → I))
      (fun _ _ h => Function.Embedding.ext (congrFun h))
    simpa only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, Nat.mul_comm, Nat.cast_pow] using (show
        (Fintype.card ((Fin q × Bool) ↪ I) : ℝ) ≤
          (Fintype.card ((Fin q × Bool) → I) : ℝ) by exact_mod_cast hle)
  calc
    _ ≤ ∑ _e : (Fin q × Bool) ↪ I, ((b : ℝ) / Fintype.card E) ^ q :=
      Finset.sum_le_sum (fun e _ => uniform_disjointPairConstraint_row_bound R b hb e)
    _ = (Fintype.card ((Fin q × Bool) ↪ I) : ℝ) * ((b : ℝ) / Fintype.card E) ^ q := by simp
    _ ≤ (Fintype.card I : ℝ) ^ (2 * q) * ((b : ℝ) / Fintype.card E) ^ q :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by rw [mul_pow, pow_mul]

end LocalLaw
