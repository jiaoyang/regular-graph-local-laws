import LocalLaw.FourPathPatternProbability
import LocalLaw.FiniteReferenceThreshold
import LocalLaw.PatternProbability
import LocalLaw.ProbabilityBudget
import LocalLaw.PolynomialFailureAbsorption

/-! Transfer all-polynomial spectral conclusions from the constructed reference
threshold to the original structural event at any smaller positive threshold.
The unconditional numerator is compared before dividing by the new denominator.
-/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance paperConditionalTransferDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Event inclusion alone does not compare conditional probabilities. The mass
bounds below recover the required factor two through the unconditional numerator. -/
theorem conditional_event_transfer {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀x,0≤w x) (A B failure : Ω → Prop)
    (hAB : ∀x,A x→B x) (hA : 1/2≤eventMass w A)
    (hBpos : 0<eventMass w B) (hB : eventMass w B≤1)
    (δ : ℝ) (hδ : 0≤δ)
    (hfailure : eventMass w (fun x=>B x∧failure x)/eventMass w B≤δ) :
    eventMass w (fun x=>A x∧failure x)/eventMass w A≤2*δ := by
  have hnum : eventMass w (fun x=>B x∧failure x)≤δ := by
    have hh := (div_le_iff₀ hBpos).mp hfailure
    exact hh.trans ((mul_le_mul_of_nonneg_left hB hδ).trans_eq (mul_one δ))
  have hsmall : eventMass w (fun x=>A x∧failure x)≤δ :=
    (eventMass_mono w hw (fun x hx=>⟨hAB x hx.1,hx.2⟩)).trans hnum
  exact conditional_budget_factor_two _ _ δ hδ hA hsmall

/-- Any actual graph event with all-power conditional control at `finiteOmega`
has the same all-power control at every positive threshold below it. -/
theorem source_conditional_transfer (d ω : ℕ) (c : ℝ)
    (hd : 3≤d) (hω : 1≤ω) (hωmax : ω≤finiteOmega d)
    (hc : 0<c) (hc1 : c<1) (good : ∀N,RegularGraph N d→Prop)
    (hgood : ∀D:ℕ,∀ᶠ N:ℕ in Filter.atTop,Nonempty (RegularGraph N d)→
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g∧¬good N g)/
      eventMass (RegularGraph.weight (N:=N) (d:=d))
        (RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊)≤1/(N:ℝ)^D) :
    ∀D:ℕ,∀ᶠ N:ℕ in Filter.atTop,Nonempty (RegularGraph N d)→
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊ g∧¬good N g)/
      eventMass (RegularGraph.weight (N:=N) (d:=d))
        (RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊)≤1/(N:ℝ)^D := by
  intro D
  filter_upwards [hgood (D+1),
    eventually_original_structural_mass_half d ω c hd hω hc hc1,
    eventually_original_structural_mass_half d (finiteOmega d) c hd (finiteOmega_positive d hd) hc hc1,
    eventually_const_div_pow_succ_le 2 D] with N hgood hmass hbase habsorb
  intro hnonempty
  have hA := hmass hnonempty
  have hB := hbase hnonempty
  have hh := conditional_event_transfer (RegularGraph.weight (N:=N) (d:=d))
    RegularGraph.weight_nonnegative
    (RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊)
    (RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊)
    (fun g=>¬good N g) (by
      intro g hg
      exact ⟨fun o=>(hg.1 o).trans hωmax,hg.2⟩)
    hA (by linarith) (finiteUniform_eventMass_le_one _)
    (1/(N:ℝ)^(D+1)) (by positivity) (hgood hnonempty)
  exact hh.trans ((by simpa only [mul_one_div] using habsorb))

/-- The paper permits an arbitrary real failure exponent. Integer all-power
bounds imply this exact, coefficient-one real-exponent version. -/
theorem source_conditional_transfer_real (d ω : ℕ) (c : ℝ)
    (hd : 3≤d) (hω : 1≤ω) (hωmax : ω≤finiteOmega d)
    (hc : 0<c) (hc1 : c<1) (good : ∀N,RegularGraph N d→Prop)
    (hgood : ∀D:ℕ,∀ᶠ N:ℕ in Filter.atTop,Nonempty (RegularGraph N d)→
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g∧¬good N g)/
      eventMass (RegularGraph.weight (N:=N) (d:=d))
        (RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊)≤1/(N:ℝ)^D) :
    ∀C:ℝ,∀ᶠ N:ℕ in Filter.atTop,Nonempty (RegularGraph N d)→
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊ g∧¬good N g)/
      eventMass (RegularGraph.weight (N:=N) (d:=d))
        (RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊)≤1/(N:ℝ)^C :=
  all_nat_polynomial_bounds_real _ _
    (source_conditional_transfer d ω c hd hω hωmax hc hc1 good hgood)

end SpectralConsequences
#print axioms SpectralConsequences.source_conditional_transfer
#print axioms SpectralConsequences.source_conditional_transfer_real
