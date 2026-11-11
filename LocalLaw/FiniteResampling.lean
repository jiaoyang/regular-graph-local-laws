import LocalLaw.Abstract

/-!
# Finite dependent resampling spaces

The enlarged sample space is the actual dependent sum `Σ g, S g`: first select
configuration `g` with weight `p g`, then select uniformly from its finite
nonempty fiber `S g`. Marginality follows by summing the fibers. Preservation
of enlarged weights follows from an invariant block with constant fiber sizes;
it is not an extra probabilistic assumption. The graph-specific involution
and its invariant-block property remain inputs.
-/

open scoped BigOperators

namespace LocalLaw

section DependentFiniteFibers

variable {Γ : Type*} [Fintype Γ]
variable (S : Γ → Type*) [∀ g, Fintype (S g)]

/-- A graph-dependent uniform fiber over an arbitrary base weight. -/
noncomputable def finiteFiberWeight (p : Γ → ℝ) (ω : Σ g, S g) : ℝ :=
  p ω.1 / (Fintype.card (S ω.1) : ℝ)

omit [Fintype Γ] in
theorem finiteFiberWeight_nonneg (p : Γ → ℝ) (hp : ∀ g, 0 ≤ p g)
    (ω : Σ g, S g) : 0 ≤ finiteFiberWeight S p ω :=
  div_nonneg (hp ω.1) (Nat.cast_nonneg _)

variable [∀ g, Nonempty (S g)]

/-- Summing the uniformly weighted nonempty fibers gives exactly the original
configuration weight, including for arbitrary events of the base space. -/
theorem finiteFiberWeight_projection (p : Γ → ℝ) (P : Γ → Prop) :
    eventMass (finiteFiberWeight S p) (fun ω => P ω.1) = eventMass p P := by
  classical
  unfold eventMass finiteFiberWeight
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : P g
  · simp only [hg, if_true]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (S g) : ℝ) ≠ 0 := by positivity
    field_simp
  · simp [hg]

/-- Total weight is preserved by the finite dependent enlargement. -/
theorem finiteFiberWeight_total (p : Γ → ℝ) :
    (∑ ω : Σ g, S g, finiteFiberWeight S p ω) = ∑ g, p g := by
  simpa only [eventMass, if_true] using finiteFiberWeight_projection S p (fun _ => True)

/-- Marginality also holds for arbitrary real-valued base observables. -/
theorem finiteFiberWeight_expectation (p f : Γ → ℝ) :
    (∑ ω : Σ g, S g, finiteFiberWeight S p ω * f ω.1) = ∑ g, p g * f g := by
  classical
  unfold finiteFiberWeight
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro g _
  dsimp only
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (S g) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Conditional probability of an event under uniform sampling in one fiber. -/
noncomputable def finiteFiberProbability (R : (Σ g, S g) → Prop) (g : Γ) : ℝ :=
  (Fintype.card (S g) : ℝ)⁻¹ * eventMass (fun _s : S g => (1 : ℝ))
    (fun s => R ⟨g, s⟩)

omit [∀ g, Nonempty (S g)] in
/-- Exact finite disintegration, including events depending on resampling data. -/
theorem finiteFiberWeight_disintegration (p : Γ → ℝ)
    (R : (Σ g, S g) → Prop) :
    eventMass (finiteFiberWeight S p) R =
      ∑ g, p g * finiteFiberProbability S R g := by
  classical
  unfold finiteFiberProbability eventMass finiteFiberWeight
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro g _
  dsimp only
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hR : R ⟨g, s⟩ <;> simp [hR, div_eq_mul_inv]

omit [Fintype Γ] [∀ g, Nonempty (S g)] in
theorem finiteFiberProbability_base_and (A : Γ → Prop) [DecidablePred A]
    (R : (Σ g, S g) → Prop) (g : Γ) :
    finiteFiberProbability S (fun ω => A ω.1 ∧ R ω) g =
      if A g then finiteFiberProbability S R g else 0 := by
  classical
  by_cases hA : A g <;> simp [finiteFiberProbability, eventMass, hA]

omit [∀ g, Nonempty (S g)] in
/-- Pointwise conditional resampling estimates integrate against the base
measure. The source event may have any base weight. -/
theorem finiteFiberWeight_conditional_error (p : Γ → ℝ)
    (hp : ∀ g, 0 ≤ p g) (A : Γ → Prop) (R : (Σ g, S g) → Prop)
    (δ : ℝ) (herror : ∀ g, A g → finiteFiberProbability S R g ≤ δ) :
    eventMass (finiteFiberWeight S p) (fun ω => A ω.1 ∧ R ω) ≤
      δ * eventMass p A := by
  classical
  rw [finiteFiberWeight_disintegration]
  unfold eventMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro g _
  rw [finiteFiberProbability_base_and]
  by_cases hA : A g
  · simp only [hA, if_true]
    calc
      p g * finiteFiberProbability S R g ≤ p g * δ :=
        mul_le_mul_of_nonneg_left (herror g hA) (hp g)
      _ = δ * p g := mul_comm _ _
  · simp [hA]

end DependentFiniteFibers

section InvariantBlocks

variable {Γ B : Type*} [Fintype Γ]
variable (S : Γ → Type*) [∀ g, Fintype (S g)]

omit [Fintype Γ] in
/-- If both the base weights and the sample-fiber cardinalities depend only on
an invariant block, every block-preserving enlarged permutation preserves the
constructed weight. No involution is needed for this marginal statement. -/
theorem finiteFiberWeight_preserved_of_block
    (p : Γ → ℝ) (block : Γ → B)
    (hp : ∀ g h, block g = block h → p g = p h)
    (hcard : ∀ g h, block g = block h → Fintype.card (S g) = Fintype.card (S h))
    (τ : Equiv.Perm (Σ g, S g))
    (hblock : ∀ ω, block (τ ω).1 = block ω.1) :
    ∀ ω, finiteFiberWeight S p (τ ω) = finiteFiberWeight S p ω := by
  intro ω
  unfold finiteFiberWeight
  rw [hp _ _ (hblock ω), hcard _ _ (hblock ω)]

/-- Constant uniform base weight. Nonemptiness is only needed to establish
that these weights have total one, not to define them. -/
noncomputable def finiteUniformWeight (Γ : Type*) [Fintype Γ] (_g : Γ) : ℝ :=
  1 / (Fintype.card Γ : ℝ)

theorem finiteUniformWeight_nonneg (g : Γ) : 0 ≤ finiteUniformWeight Γ g := by
  unfold finiteUniformWeight
  positivity

theorem finiteUniformWeight_total [Nonempty Γ] :
    (∑ g : Γ, finiteUniformWeight Γ g) = 1 := by
  classical
  unfold finiteUniformWeight
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card Γ : ℝ) ≠ 0 := by positivity
  field_simp

/-- The paper's setting: all graphs are uniform, and sample-fiber cardinality
is constant on the preserved neighborhood block. -/
theorem uniform_finiteFiberWeight_preserved
    (block : Γ → B)
    (hcard : ∀ g h, block g = block h → Fintype.card (S g) = Fintype.card (S h))
    (τ : Equiv.Perm (Σ g, S g))
    (hblock : ∀ ω, block (τ ω).1 = block ω.1) :
    ∀ ω, finiteFiberWeight S (finiteUniformWeight Γ) (τ ω) =
      finiteFiberWeight S (finiteUniformWeight Γ) ω :=
  finiteFiberWeight_preserved_of_block S (finiteUniformWeight Γ) block
    (fun _ _ _ => rfl) hcard τ hblock

variable [∀ g, Nonempty (S g)]

/-- Normalization of the actual enlarged uniform sample space. -/
theorem uniform_finiteFiberWeight_total [Nonempty Γ] :
    (∑ ω : Σ g, S g, finiteFiberWeight S (finiteUniformWeight Γ) ω) = 1 := by
  rw [finiteFiberWeight_total, finiteUniformWeight_total]

/-- The reversible two-stage transfer for the constructed dependent enlarged
space. Its marginal and weight-preservation hypotheses are derived from the
construction rather than assumed separately. -/
theorem finite_fiber_reversible_two_stage
    (p : Γ → ℝ) (hpnonneg : ∀ g, 0 ≤ p g) (block : Γ → B)
    (hp : ∀ g h, block g = block h → p g = p h)
    (hcard : ∀ g h, block g = block h → Fintype.card (S g) = Fintype.card (S h))
    (τ : Equiv.Perm (Σ g, S g))
    (hblock : ∀ ω, block (τ ω).1 = block ω.1)
    (hinv : Function.Involutive τ) (A B C : Γ → Prop) (α γ : ℝ)
    (hfirst : eventMass (finiteFiberWeight S p)
      (fun ω => A ω.1 ∧ ¬ B (τ ω).1) ≤ α)
    (hsecond : eventMass (finiteFiberWeight S p)
      (fun ω => B ω.1 ∧ ¬ C (τ ω).1) ≤ γ) :
    eventMass p (fun g => A g ∧ ¬ C g) ≤ α + γ := by
  rw [← finiteFiberWeight_projection S p (fun g => A g ∧ ¬ C g)]
  exact reversible_two_stage (finiteFiberWeight S p)
    (finiteFiberWeight_nonneg S p hpnonneg) τ
    (finiteFiberWeight_preserved_of_block S p block hp hcard τ hblock) hinv
    (fun ω => A ω.1) (fun ω => B ω.1) (fun ω => C ω.1) α γ hfirst hsecond

omit [∀ g, Nonempty (S g)] in
/-- A uniform graphwise conditional error is also an unconditional error. -/
theorem uniform_finiteFiberWeight_conditional_error [Nonempty Γ]
    (A : Γ → Prop) (R : (Σ g, S g) → Prop) (δ : ℝ) (hδ : 0 ≤ δ)
    (herror : ∀ g, A g → finiteFiberProbability S R g ≤ δ) :
    eventMass (finiteFiberWeight S (finiteUniformWeight Γ))
      (fun ω => A ω.1 ∧ R ω) ≤ δ := by
  have hmass : eventMass (finiteUniformWeight Γ) A ≤ 1 := by
    calc
      eventMass (finiteUniformWeight Γ) A ≤
          eventMass (finiteUniformWeight Γ) (fun _ => True) :=
        eventMass_mono _ finiteUniformWeight_nonneg (fun _ _ => True.intro)
      _ = 1 := by
        simpa only [eventMass, if_true] using (finiteUniformWeight_total (Γ := Γ))
  calc
    eventMass (finiteFiberWeight S (finiteUniformWeight Γ))
        (fun ω => A ω.1 ∧ R ω)
        ≤ δ * eventMass (finiteUniformWeight Γ) A :=
      finiteFiberWeight_conditional_error S (finiteUniformWeight Γ)
        finiteUniformWeight_nonneg A R δ herror
    _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hmass hδ
    _ = δ := mul_one _

/-- Two-stage reversible transfer directly from graphwise conditional errors
on the actual dependent sample fibers, for the uniform base ensemble. -/
theorem uniform_finite_fiber_reversible_two_stage [Nonempty Γ]
    (block : Γ → B)
    (hcard : ∀ g h, block g = block h → Fintype.card (S g) = Fintype.card (S h))
    (τ : Equiv.Perm (Σ g, S g))
    (hblock : ∀ ω, block (τ ω).1 = block ω.1)
    (hinv : Function.Involutive τ) (A B C : Γ → Prop) (α γ : ℝ)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hfirst : ∀ g, A g →
      finiteFiberProbability S (fun ω => ¬ B (τ ω).1) g ≤ α)
    (hsecond : ∀ g, B g →
      finiteFiberProbability S (fun ω => ¬ C (τ ω).1) g ≤ γ) :
    eventMass (finiteUniformWeight Γ) (fun g => A g ∧ ¬ C g) ≤ α + γ := by
  apply finite_fiber_reversible_two_stage S (finiteUniformWeight Γ)
    finiteUniformWeight_nonneg block (fun _ _ _ => rfl) hcard τ hblock hinv
    A B C α γ
  · exact uniform_finiteFiberWeight_conditional_error S A
      (fun ω => ¬ B (τ ω).1) α hα hfirst
  · exact uniform_finiteFiberWeight_conditional_error S B
      (fun ω => ¬ C (τ ω).1) γ hγ hsecond

end InvariantBlocks

end LocalLaw
