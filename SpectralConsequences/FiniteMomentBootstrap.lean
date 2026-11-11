import Mathlib

/-!
# A finite high-moment recurrence solver

The input is a recurrence between actual moments, not a tail estimate.
The proof absorbs its lower moments by an elementary power comparison, so
neither a probability-space embedding nor fractional powers are needed.
-/

open scoped BigOperators
noncomputable section
namespace SpectralConsequences

/-- A mixed power is controlled by the two endpoint powers. -/
theorem mixed_power_le_endpoint_sum (x T : ℝ) (hx : 0 ≤ x) (hT : 0 ≤ T)
    (n j : ℕ) (hj : j ≤ n) :
    T ^ j * x ^ (n - j) ≤ T ^ n + x ^ n := by
  by_cases h : x ≤ T
  · calc
      T ^ j * x ^ (n-j) ≤ T ^ j * T ^ (n-j) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx h _) (pow_nonneg hT _)
      _ = T ^ n := by rw [← pow_add, Nat.add_sub_of_le hj]
      _ ≤ _ := le_add_of_nonneg_right (pow_nonneg hx _)
  · have h' : T ≤ x := le_of_lt (lt_of_not_ge h)
    calc
      T ^ j * x ^ (n-j) ≤ x ^ j * x ^ (n-j) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT h' _) (pow_nonneg hx _)
      _ = x ^ n := by rw [← pow_add, Nat.add_sub_of_le hj]
      _ ≤ _ := le_add_of_nonneg_left (pow_nonneg hT _)

/-- A coefficient budget makes every term of a moment recurrence absorbable. -/
theorem weighted_lower_moment_absorption {Ω : Type*} [Fintype Ω]
    (w f : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hf : ∀ ω, 0 ≤ f ω)
    (hwtotal : ∑ ω, w ω ≤ 1) (n j : ℕ) (hj : j ≤ n)
    (T c D : ℝ) (hT : 0 ≤ T)
    (hbudget : D * c ≤ T ^ j) :
    D * (c * (∑ ω, w ω * f ω ^ (n-j))) ≤
      T ^ n + ∑ ω, w ω * f ω ^ n := by
  calc
    _ = ∑ ω, w ω * (D * c * f ω ^ (n-j)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ ≤ ∑ ω, w ω * (T ^ n + f ω ^ n) := by
      apply Finset.sum_le_sum
      intro ω _
      apply mul_le_mul_of_nonneg_left _ (hw ω)
      exact (mul_le_mul_of_nonneg_right hbudget (pow_nonneg (hf ω) _)).trans
        (mixed_power_le_endpoint_sum (f ω) T (hf ω) hT n j hj)
    _ = (∑ ω, w ω) * T ^ n + ∑ ω, w ω * f ω ^ n := by
      simp [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ _ := add_le_add_right (mul_le_of_le_one_left (pow_nonneg hT _) hwtotal) _

/-- An actual moment recurrence of length n yields an n-th moment bound.
There is no positivity assumption on T: T=0 is allowed. -/
theorem finite_moment_recurrence_bound {Ω : Type*} [Fintype Ω]
    (w f : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hf : ∀ ω, 0 ≤ f ω)
    (hwtotal : ∑ ω, w ω ≤ 1) (n : ℕ) (hn : 0 < n)
    (c : Fin n → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hbudget : ∀ j, (4 * (n : ℝ)) * c j ≤ T ^ (j.val+1))
    (hrecurrence : (∑ ω, w ω * f ω ^ n) ≤
      ∑ j : Fin n, c j * (∑ ω, w ω * f ω ^ (n-(j.val+1)))) :
    (∑ ω, w ω * f ω ^ n) ≤ T ^ n := by
  let M := ∑ ω, w ω * f ω ^ n
  have hM : 0 ≤ M := Finset.sum_nonneg (fun ω _ => mul_nonneg (hw ω) (pow_nonneg (hf ω) _))
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hterm (j : Fin n) :
      (4 * (n : ℝ)) * (c j * (∑ ω, w ω * f ω ^ (n-(j.val+1)))) ≤ T ^ n + M := by
    exact weighted_lower_moment_absorption w f hw hf hwtotal n (j.val+1)
      (by omega) T (c j) (4*(n:ℝ)) hT (hbudget j)
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hterm j)
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hs
  have hrec : M ≤ ∑ j : Fin n, c j * (∑ ω, w ω * f ω ^ (n-(j.val+1))) := hrecurrence
  have hscaled := mul_le_mul_of_nonneg_left hrec (show 0 ≤ 4*(n:ℝ) by positivity)
  have hfinal : 4 * M ≤ T ^ n + M := by nlinarith
  dsimp only [M] at hM hfinal ⊢
  linarith [pow_nonneg hT n]

/-- Truncation to an event preserves the subprobability hypothesis used by
the recurrence solver. This is the moment measure in Proposition 7.2. -/
theorem event_weight_subprobability {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hprob : ∑ ω, w ω ≤ 1)
    (A : Ω → Prop) [DecidablePred A] :
    (∀ ω, 0 ≤ (if A ω then w ω else 0)) ∧
      (∑ ω, if A ω then w ω else 0) ≤ 1 := by
  constructor
  · intro ω
    split_ifs
    · exact hw ω
    · exact le_rfl
  · refine (Finset.sum_le_sum (fun ω _ => ?_)).trans hprob
    split_ifs <;> simp_all

end SpectralConsequences
