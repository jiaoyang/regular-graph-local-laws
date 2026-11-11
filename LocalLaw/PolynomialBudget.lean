import LocalLaw.ProbabilityBudget

/-!
# Arbitrary polynomial net-size probability budgets

A finer branch-aware spectral net may use a different polynomial number of
nodes. The union-bound cost is the sum of the node and center exponents;
it is not restricted to the paper's particular cubic bookkeeping.
-/

open scoped BigOperators

namespace LocalLaw

theorem polynomial_probability_budget {T O : Type*} [Fintype T]
    (centers : T → Finset O) (α γ : T → O → ℝ)
    (N q p k : ℕ) (hN : 0 < N) (hq : p + k ≤ q)
    (Cgrid Ccenter D : ℝ) (hCcenter : 0 ≤ Ccenter) (hD : 0 ≤ D)
    (hnode : (Fintype.card T : ℝ) ≤ Cgrid * (N : ℝ) ^ p)
    (hcenter : ∀ t, ((centers t).card : ℝ) ≤ Ccenter * (N : ℝ) ^ k)
    (hα : ∀ t o, o ∈ centers t → α t o ≤ D / (N : ℝ) ^ q)
    (hγ : ∀ t o, o ∈ centers t → γ t o ≤ D / (N : ℝ) ^ q) :
    (∑ t, ∑ o ∈ centers t, (α t o + γ t o)) ≤
      2 * Cgrid * Ccenter * D / (N : ℝ) ^ (q - (p + k)) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNzero : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hraw := finite_double_budget_bound centers (fun t o => α t o + γ t o)
    (Cgrid * (N : ℝ) ^ p) (Ccenter * (N : ℝ) ^ k) (2 * D / (N : ℝ) ^ q)
    (by positivity) (by positivity) hnode hcenter (by
      intro t o ho
      calc
        _ ≤ D / (N : ℝ) ^ q + D / (N : ℝ) ^ q := add_le_add (hα t o ho) (hγ t o ho)
        _ = 2 * D / (N : ℝ) ^ q := by ring)
  have hpower : (N : ℝ) ^ q = (N : ℝ) ^ (q - (p + k)) * (N : ℝ) ^ (p + k) := by
    rw [← pow_add]
    congr 1
    omega
  have halgebra : (Cgrid * (N : ℝ) ^ p) * (Ccenter * (N : ℝ) ^ k) *
      (2 * D / (N : ℝ) ^ q) =
      2 * Cgrid * Ccenter * D / (N : ℝ) ^ (q - (p + k)) := by
    rw [hpower, pow_add]
    field_simp [hNzero]
    ring
  exact hraw.trans_eq halgebra

namespace AssemblyInputs

variable {X O Z : Type*} [Fintype X] {T : ℕ}

theorem uniform_failure_arbitrary_polynomial (S : AssemblyInputs X O Z T)
    (N q p k : ℕ) (hN : 0 < N) (hq : p + k ≤ q)
    (Cgrid Ccenter D : ℝ) (hCcenter : 0 ≤ Ccenter) (hD : 0 ≤ D)
    (hnode : (T : ℝ) ≤ Cgrid * (N : ℝ) ^ p)
    (hcenter : ∀ t, ((S.centers t).card : ℝ) ≤ Ccenter * (N : ℝ) ^ k)
    (hα : ∀ t o, o ∈ S.centers t → S.firstBudget t o ≤ D / (N : ℝ) ^ q)
    (hγ : ∀ t o, o ∈ S.centers t → S.secondBudget t o ≤ D / (N : ℝ) ^ q) :
    eventMass S.weight (fun x => S.structural x ∧ ¬ ∀ z ∈ S.domain, S.regular z x) ≤
      2 * Cgrid * Ccenter * D / (N : ℝ) ^ (q - (p + k)) := by
  apply S.uniform_failure_bound.trans
  apply polynomial_probability_budget S.centers S.firstBudget S.secondBudget N q p k hN hq
    Cgrid Ccenter D hCcenter hD
  · simpa only [Fintype.card_fin] using hnode
  · exact hcenter
  · exact hα
  · exact hγ

end AssemblyInputs

end LocalLaw
