import Mathlib

/-!
# Abstract components of a resampling local-law proof

These are conditional, model-independent lemmas inspired by the proof of
Theorem 4.2 in Huang--Yau, arXiv:2102.00963v3, especially Section 4.3.
They do not formalize the graph estimates, the quadratic stability argument,
or Theorem 4.2 itself. All model-dependent inputs are explicit hypotheses.

Checked with Lean 4.19.0 and mathlib v4.19.0. No added axioms or `sorry`.
-/

open scoped BigOperators

namespace LocalLaw

section FiniteMass

variable {Ω : Type*} [Fintype Ω]

/-- Mass of an event under finite nonnegative weights. The weights need not
sum to one, so this also applies to restrictions to an ambient good event. -/
noncomputable def eventMass (w : Ω → ℝ) (P : Ω → Prop) : ℝ := by
  classical
  exact ∑ x, if P x then w x else 0

theorem eventMass_mono (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    {P Q : Ω → Prop} (hPQ : ∀ x, P x → Q x) :
    eventMass w P ≤ eventMass w Q := by
  classical
  unfold eventMass
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : P x
  · simp [hp, hPQ x hp]
  · by_cases hq : Q x <;> simp [hp, hq, hw x]

theorem eventMass_union_le (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (P Q : Ω → Prop) :
    eventMass w (fun x => P x ∨ Q x) ≤ eventMass w P + eventMass w Q := by
  classical
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq, hw x]

/-- Change of variables for a weight-preserving permutation. -/
theorem eventMass_pullback (w : Ω → ℝ) (φ : Equiv.Perm Ω)
    (hwφ : ∀ x, w (φ x) = w x) (P : Ω → Prop) :
    eventMass w (fun x => P (φ x)) = eventMass w P := by
  classical
  unfold eventMass
  apply Fintype.sum_equiv φ
  intro x
  rw [hwφ x]

/-- The reversible two-stage argument in (4.27)--(4.30).

The permutation acts on the enlarged space of a graph together with its
resampling data. One uses a single involution twice; no independence between
the two stages is assumed. -/
theorem reversible_two_stage (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (φ : Equiv.Perm Ω) (hwφ : ∀ x, w (φ x) = w x)
    (hφ : Function.Involutive φ) (A B C : Ω → Prop) (δ₁ δ₂ : ℝ)
    (h₁ : eventMass w (fun x => A x ∧ ¬ B (φ x)) ≤ δ₁)
    (h₂ : eventMass w (fun x => B x ∧ ¬ C (φ x)) ≤ δ₂) :
    eventMass w (fun x => A x ∧ ¬ C x) ≤ δ₁ + δ₂ := by
  classical
  have hcover : ∀ x, (A x ∧ ¬ C x) →
      (A x ∧ ¬ B (φ x)) ∨ (B (φ x) ∧ ¬ C (φ (φ x))) := by
    intro x hx
    by_cases hb : B (φ x)
    · exact Or.inr ⟨hb, by simpa [hφ x] using hx.2⟩
    · exact Or.inl ⟨hx.1, hb⟩
  calc
    eventMass w (fun x => A x ∧ ¬ C x)
        ≤ eventMass w (fun x =>
          (A x ∧ ¬ B (φ x)) ∨ (B (φ x) ∧ ¬ C (φ (φ x)))) :=
      eventMass_mono w hw hcover
    _ ≤ eventMass w (fun x => A x ∧ ¬ B (φ x)) +
          eventMass w (fun x => B (φ x) ∧ ¬ C (φ (φ x))) :=
      eventMass_union_le w hw _ _
    _ = eventMass w (fun x => A x ∧ ¬ B (φ x)) +
          eventMass w (fun x => B x ∧ ¬ C (φ x)) := by
      rw [eventMass_pullback w φ hwφ (fun x => B x ∧ ¬ C (φ x))]
    _ ≤ δ₁ + δ₂ := add_le_add h₁ h₂

/-- Finite union bound for finite weighted spaces, with arbitrary event index. -/
theorem eventMass_exists_finset_le {ι : Type*} (s : Finset ι)
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (P : ι → Ω → Prop) :
    eventMass w (fun x => ∃ i ∈ s, P i x) ≤ ∑ i ∈ s, eventMass w (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eventMass]
  | @insert i s hi ih =>
      have hevent : (fun x => ∃ j ∈ insert i s, P j x) =
          (fun x => P i x ∨ ∃ j ∈ s, P j x) := by
        funext x
        simp
      rw [hevent, Finset.sum_insert hi]
      exact (eventMass_union_le w hw _ _).trans (add_le_add_left ih _)

end FiniteMass

section Bootstrap

variable {Ω : Type*}

/-- First-failure inclusion for a finite chain. A grid is handled by indexing
one chain per horizontal coordinate, then taking a finite union of chains.
`Strong` is the half-size event and `Weak` is the full-size event. -/
theorem first_failure (K : ℕ) (Base : Ω → Prop)
    (Strong Weak : ℕ → Ω → Prop)
    (hbase : ∀ x, Base x → Strong 0 x)
    (hstep : ∀ k < K, ∀ x, Strong k x → Weak (k + 1) x)
    (x : Ω) (hx : Base x ∧ ¬ (∀ k ≤ K, Strong k x)) :
    ∃ k ∈ Finset.range K, Weak (k + 1) x ∧ ¬ Strong (k + 1) x := by
  classical
  by_contra hnone
  have hall : ∀ k, k ≤ K → Strong k x := by
    intro k
    induction k with
    | zero => exact fun _ => hbase x hx.1
    | succ k ih =>
        intro hk
        have hklt : k < K := by omega
        have hweak : Weak (k + 1) x := hstep k hklt x (ih (by omega))
        by_contra hstrong
        exact hnone ⟨k, Finset.mem_range.mpr hklt, hweak, hstrong⟩
  exact hx.2 hall

/-- Probability/mass loss is the sum of local improvement defects. There is
no multiplicative loss from the number of induction steps. -/
theorem bootstrap_mass_bound [Fintype Ω] (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (K : ℕ) (Base : Ω → Prop) (Strong Weak : ℕ → Ω → Prop)
    (hbase : ∀ x, Base x → Strong 0 x)
    (hstep : ∀ k < K, ∀ x, Strong k x → Weak (k + 1) x)
    (δ : ℕ → ℝ)
    (hdefect : ∀ k < K,
      eventMass w (fun x => Weak (k + 1) x ∧ ¬ Strong (k + 1) x) ≤ δ k) :
    eventMass w (fun x => Base x ∧ ¬ (∀ k ≤ K, Strong k x)) ≤
      ∑ k ∈ Finset.range K, δ k := by
  classical
  calc
    eventMass w (fun x => Base x ∧ ¬ (∀ k ≤ K, Strong k x))
        ≤ eventMass w (fun x => ∃ k ∈ Finset.range K,
          Weak (k + 1) x ∧ ¬ Strong (k + 1) x) :=
      eventMass_mono w hw (fun x hx => first_failure K Base Strong Weak hbase hstep x hx)
    _ ≤ ∑ k ∈ Finset.range K,
          eventMass w (fun x => Weak (k + 1) x ∧ ¬ Strong (k + 1) x) :=
      eventMass_exists_finset_le _ w hw _
    _ ≤ ∑ k ∈ Finset.range K, δ k := by
      apply Finset.sum_le_sum
      intro k hk
      exact hdefect k (Finset.mem_range.mp hk)

end Bootstrap

section DeterministicTransfer

variable {E : Type*} [SeminormedAddCommGroup E]
variable {Boundary : Type*} [PseudoMetricSpace Boundary]

/-- Transfer from a random boundary parameter to the deterministic one.
This is the abstract final triangle inequality in the proof of Theorem 4.2. -/
theorem model_transfer (G : E) (P : Boundary → E) (q m : Boundary)
    (ε L Δ : ℝ) (hL : 0 ≤ L)
    (happrox : ‖G - P q‖ ≤ ε)
    (hboundary : dist q m ≤ Δ)
    (hmodel : ‖P q - P m‖ ≤ L * dist q m) :
    ‖G - P m‖ ≤ ε + L * Δ := by
  calc
    ‖G - P m‖ ≤ ‖G - P q‖ + ‖P q - P m‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε + L * Δ := add_le_add happrox (hmodel.trans (mul_le_mul_of_nonneg_left hboundary hL))

end DeterministicTransfer

section SparseAverage

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
variable [SeminormedAddCommGroup E]

/-- A sparse set of exceptional diagonals contributes its density times
its additional error. Use `f i = G i i - m` in a local-law application. -/
theorem sparse_sum_bound (f : ι → E) (bad : Finset ι) (a b : ℝ)
    (hgood : ∀ i, i ∉ bad → ‖f i‖ ≤ a)
    (hbad : ∀ i, i ∈ bad → ‖f i‖ ≤ a + b) :
    ‖∑ i, f i‖ ≤ (Fintype.card ι : ℝ) * a + (bad.card : ℝ) * b := by
  classical
  calc
    ‖∑ i, f i‖ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ i, (a + if i ∈ bad then b else 0) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ bad
      · simpa [hi] using hbad i hi
      · simpa [hi] using hgood i hi
    _ = (Fintype.card ι : ℝ) * a + (bad.card : ℝ) * b := by
      simp [Finset.sum_add_distrib, ← Finset.sum_filter, nsmul_eq_mul]

variable [NormedSpace ℝ E]

/-- Normalized version of `sparse_sum_bound`, with the cardinality assumed
positive explicitly, as it must be before taking an empirical average. -/
theorem sparse_average_bound (f : ι → E) (bad : Finset ι) (a b : ℝ)
    (hcard : 0 < Fintype.card ι)
    (hgood : ∀ i, i ∉ bad → ‖f i‖ ≤ a)
    (hbad : ∀ i, i ∈ bad → ‖f i‖ ≤ a + b) :
    ‖(Fintype.card ι : ℝ)⁻¹ • ∑ i, f i‖ ≤
      a + ((bad.card : ℝ) / (Fintype.card ι : ℝ)) * b := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr hcard
  calc
    ‖(Fintype.card ι : ℝ)⁻¹ • ∑ i, f i‖
        = (Fintype.card ι : ℝ)⁻¹ * ‖∑ i, f i‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le)]
    _ ≤ (Fintype.card ι : ℝ)⁻¹ *
          ((Fintype.card ι : ℝ) * a + (bad.card : ℝ) * b) :=
      mul_le_mul_of_nonneg_left (sparse_sum_bound f bad a b hgood hbad)
        (inv_nonneg.mpr hn.le)
    _ = a + ((bad.card : ℝ) / (Fintype.card ι : ℝ)) * b := by
      field_simp
      ring

end SparseAverage

end LocalLaw
