import LocalLaw.StrongBadCenterProbability
import LocalLaw.ProbabilityBudget

/-!
# Recover the original structural conditioning after an auxiliary event

The proof may run on a stronger good event. Its failure probability under the
original conditional law is the auxiliary-event loss plus the stronger-event
failure, with the original denominator retained explicitly.
-/

namespace LocalLaw
section
variable {X : Type*} [Fintype X]

/-- Exact event-cover bookkeeping for a strengthened bootstrap event. -/
theorem strengthened_event_failure_mass (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (original strong failure : X → Prop) (α β : ℝ)
    (loss : eventMass w (fun x => original x ∧ ¬ strong x) ≤ α)
    (inside : eventMass w (fun x => strong x ∧ failure x) ≤ β) :
    eventMass w (fun x => original x ∧ failure x) ≤ α + β := by
  apply (eventMass_mono w hw
    (P := fun x => original x ∧ failure x)
    (Q := fun x => (original x ∧ ¬ strong x) ∨ (strong x ∧ failure x)) (by
    intro x hx
    by_cases hs : strong x
    · exact Or.inr ⟨hs, hx.2⟩
    · exact Or.inl ⟨hx.1, hs⟩)).trans
  exact (eventMass_union_le w hw _ _).trans (add_le_add loss inside)

/-- A lower mass for the original event and a small auxiliary loss give a
positive stronger-event mass, rather than assuming one separately. -/
theorem strengthened_event_mass_lower (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (original strong : X → Prop)
    (mass : 1 / 2 ≤ eventMass w original)
    (loss : eventMass w (fun x => original x ∧ ¬ strong x) ≤ 1 / 4) :
    1 / 4 ≤ eventMass w strong := by
  have hcover : eventMass w original ≤
      eventMass w (fun x => original x ∧ ¬ strong x) + eventMass w strong := by
    apply (eventMass_mono w hw (P := original)
      (Q := fun x => (original x ∧ ¬ strong x) ∨ strong x) (by
      intro x hx
      by_cases hs : strong x
      · exact Or.inr hs
      · exact Or.inl ⟨hx, hs⟩)).trans
    exact eventMass_union_le w hw _ _
  linarith

theorem strengthened_event_conditional_failure (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (original strong failure : X → Prop) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (mass : 1 / 2 ≤ eventMass w original)
    (loss : eventMass w (fun x => original x ∧ ¬ strong x) ≤ α)
    (inside : eventMass w (fun x => strong x ∧ failure x) ≤ β) :
    eventMass w (fun x => original x ∧ failure x) / eventMass w original ≤ 2 * α + 2 * β := by
  have h := conditional_budget_factor_two _ _ _ (add_nonneg hα hβ) mass
    (strengthened_event_failure_mass w hw original strong failure α β loss inside)
  convert h using 1
  ring
end

/-- The actual strengthened graph event returns the desired probability
under the ORIGINAL uniform structural conditioning. -/
theorem eventually_original_structural_failure_transfer (d ω p : ℕ) (c γ : ℝ)
    (hd : 3 ≤ d) (hc : 0 ≤ c) (hγ : 3 * c / 4 < γ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (badCount : ℕ) (failure : RegularGraph N d → Prop) (β : ℝ),
      0 ≤ β →
      1 / 2 ≤ eventMass (RegularGraph.weight (N := N) (d := d))
        (RegularGraph.structural (logarithmicRadius (c / 4) d N) ω badCount) →
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        RegularGraph.structural (logarithmicRadius (c / 4) d N) ω ⌊(N : ℝ) ^ γ⌋₊ g ∧ failure g) ≤ β →
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        RegularGraph.structural (logarithmicRadius (c / 4) d N) ω badCount g ∧ failure g) /
          eventMass (RegularGraph.weight (N := N) (d := d))
            (RegularGraph.structural (logarithmicRadius (c / 4) d N) ω badCount) ≤
        2 / (N : ℝ) ^ p + 2 * β := by
  filter_upwards [eventually_strengthened_structural_difference d ω p c γ hd hc hγ] with N htail
  intro badCount failure β hβ mass inside
  have h := strengthened_event_conditional_failure RegularGraph.weight RegularGraph.weight_nonnegative
    (RegularGraph.structural (logarithmicRadius (c / 4) d N) ω badCount)
    (RegularGraph.structural (logarithmicRadius (c / 4) d N) ω ⌊(N : ℝ) ^ γ⌋₊)
    failure (1 / (N : ℝ) ^ p) β (by positivity) hβ mass (htail badCount) inside
  convert h using 1
  ring

end LocalLaw
