import LocalLaw.Assembly

/-!
# Explicit probability budgets for a spectral bootstrap

The finite theorem below proves the cubic union-bound loss rather than hiding
it in asymptotic notation. With O(N²) net nodes, O(N) centers, and two errors
of size D/N^q per node and center, the failure budget is at most
2*Cgrid*Ccenter*D/N^(q-3). Conditioning on structural mass at least 1/2 costs
at most another factor two.
-/

open scoped BigOperators

namespace LocalLaw

/-- Finite double-union arithmetic with inhomogeneous center sets. -/
theorem finite_double_budget_bound {T O : Type*} [Fintype T]
    (centers : T → Finset O) (budget : T → O → ℝ)
    (nodeCap centerCap δ : ℝ) (hcenterCap : 0 ≤ centerCap) (hδ : 0 ≤ δ)
    (hnode : (Fintype.card T : ℝ) ≤ nodeCap)
    (hcenter : ∀ t, ((centers t).card : ℝ) ≤ centerCap)
    (hbudget : ∀ t o, o ∈ centers t → budget t o ≤ δ) :
    (∑ t, ∑ o ∈ centers t, budget t o) ≤ nodeCap * centerCap * δ := by
  have hinner : ∀ t, (∑ o ∈ centers t, budget t o) ≤ centerCap * δ := by
    intro t
    calc
      (∑ o ∈ centers t, budget t o) ≤ ∑ _o ∈ centers t, δ :=
        Finset.sum_le_sum (fun o ho => hbudget t o ho)
      _ = ((centers t).card : ℝ) * δ := by simp [nsmul_eq_mul]
      _ ≤ centerCap * δ := mul_le_mul_of_nonneg_right (hcenter t) hδ
  calc
    (∑ t, ∑ o ∈ centers t, budget t o) ≤ ∑ _t : T, centerCap * δ :=
      Finset.sum_le_sum (fun t _ => hinner t)
    _ = (Fintype.card T : ℝ) * (centerCap * δ) := by simp [nsmul_eq_mul]
    _ ≤ nodeCap * (centerCap * δ) :=
      mul_le_mul_of_nonneg_right hnode (mul_nonneg hcenterCap hδ)
    _ = nodeCap * centerCap * δ := by ring

/-- The exact finite-N cubic loss for a two-stage local resampling estimate. -/
theorem cubic_probability_budget {T O : Type*} [Fintype T]
    (centers : T → Finset O) (α γ : T → O → ℝ)
    (N q : ℕ) (hN : 0 < N) (hq : 3 ≤ q)
    (Cgrid Ccenter D : ℝ) (hCcenter : 0 ≤ Ccenter) (hD : 0 ≤ D)
    (hnode : (Fintype.card T : ℝ) ≤ Cgrid * (N : ℝ) ^ 2)
    (hcenter : ∀ t, ((centers t).card : ℝ) ≤ Ccenter * (N : ℝ))
    (hα : ∀ t o, o ∈ centers t → α t o ≤ D / (N : ℝ) ^ q)
    (hγ : ∀ t o, o ∈ centers t → γ t o ≤ D / (N : ℝ) ^ q) :
    (∑ t, ∑ o ∈ centers t, (α t o + γ t o)) ≤
      2 * Cgrid * Ccenter * D / (N : ℝ) ^ (q - 3) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNzero : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hraw := finite_double_budget_bound centers (fun t o => α t o + γ t o)
    (Cgrid * (N : ℝ) ^ 2) (Ccenter * (N : ℝ)) (2 * D / (N : ℝ) ^ q)
    (mul_nonneg hCcenter hNpos.le) (by positivity) hnode hcenter (by
      intro t o ho
      calc
        α t o + γ t o ≤ D / (N : ℝ) ^ q + D / (N : ℝ) ^ q :=
          add_le_add (hα t o ho) (hγ t o ho)
        _ = 2 * D / (N : ℝ) ^ q := by ring)
  have hpower : (N : ℝ) ^ q = (N : ℝ) ^ (q - 3) * (N : ℝ) ^ 3 := by
    rw [← pow_add]
    congr 1
    omega
  have halgebra : (Cgrid * (N : ℝ) ^ 2) * (Ccenter * (N : ℝ)) *
      (2 * D / (N : ℝ) ^ q) =
      2 * Cgrid * Ccenter * D / (N : ℝ) ^ (q - 3) := by
    rw [hpower]
    field_simp [hNzero]
    ring
  exact hraw.trans_eq halgebra

/-- A structural event of mass at least one half costs at most a factor two.
This applies to a failure mass without assuming normalization of other weights. -/
theorem conditional_budget_factor_two (failure mass budget : ℝ)
    (hbudget : 0 ≤ budget) (hmass : 1 / 2 ≤ mass)
    (hfailure : failure ≤ budget) : failure / mass ≤ 2 * budget := by
  have hmasspos : 0 < mass := by linarith
  apply (div_le_iff₀ hmasspos).2
  apply hfailure.trans
  nlinarith [mul_le_mul_of_nonneg_left hmass hbudget]

namespace AssemblyInputs

variable {X O Z : Type*} [Fintype X] {T : ℕ}

/-- The actual assembly failure event has the explicit N^{-q+3} budget. -/
theorem uniform_failure_polynomial_bound (S : AssemblyInputs X O Z T)
    (N q : ℕ) (hN : 0 < N) (hq : 3 ≤ q)
    (Cgrid Ccenter D : ℝ) (hCcenter : 0 ≤ Ccenter) (hD : 0 ≤ D)
    (hnode : (T : ℝ) ≤ Cgrid * (N : ℝ) ^ 2)
    (hcenter : ∀ t, ((S.centers t).card : ℝ) ≤ Ccenter * (N : ℝ))
    (hα : ∀ t o, o ∈ S.centers t → S.firstBudget t o ≤ D / (N : ℝ) ^ q)
    (hγ : ∀ t o, o ∈ S.centers t → S.secondBudget t o ≤ D / (N : ℝ) ^ q) :
    eventMass S.weight (fun x => S.structural x ∧ ¬ ∀ z ∈ S.domain, S.regular z x)
      ≤ 2 * Cgrid * Ccenter * D / (N : ℝ) ^ (q - 3) := by
  apply S.uniform_failure_bound.trans
  apply cubic_probability_budget S.centers S.firstBudget S.secondBudget N q hN hq
    Cgrid Ccenter D hCcenter hD
  · simpa only [Fintype.card_fin] using hnode
  · exact hcenter
  · exact hα
  · exact hγ

/-- Conditional failure estimate with both the cubic net loss and structural
conditioning written as explicit finite constants. -/
theorem conditional_failure_polynomial_bound (S : AssemblyInputs X O Z T)
    (N q : ℕ) (hN : 0 < N) (hq : 3 ≤ q)
    (Cgrid Ccenter D : ℝ) (hCgrid : 0 ≤ Cgrid) (hCcenter : 0 ≤ Ccenter)
    (hD : 0 ≤ D) (hmass : 1 / 2 ≤ eventMass S.weight S.structural)
    (hnode : (T : ℝ) ≤ Cgrid * (N : ℝ) ^ 2)
    (hcenter : ∀ t, ((S.centers t).card : ℝ) ≤ Ccenter * (N : ℝ))
    (hα : ∀ t o, o ∈ S.centers t → S.firstBudget t o ≤ D / (N : ℝ) ^ q)
    (hγ : ∀ t o, o ∈ S.centers t → S.secondBudget t o ≤ D / (N : ℝ) ^ q) :
    eventMass S.weight (fun x => S.structural x ∧ ¬ ∀ z ∈ S.domain, S.regular z x) /
      eventMass S.weight S.structural ≤
      4 * Cgrid * Ccenter * D / (N : ℝ) ^ (q - 3) := by
  have hbase := uniform_failure_polynomial_bound S N q hN hq Cgrid Ccenter D
    hCcenter hD hnode hcenter hα hγ
  have hbudget : 0 ≤ 2 * Cgrid * Ccenter * D / (N : ℝ) ^ (q - 3) := by positivity
  have := conditional_budget_factor_two _ _ _ hbudget hmass hbase
  convert this using 1
  ring

end AssemblyInputs

end LocalLaw
