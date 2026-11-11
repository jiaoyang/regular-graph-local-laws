import SpectralConsequences.ExchangeableFinite
import LocalLaw.GraphConcentration

/-! # Complex disintegration and graph-law marginality

The event marginality of the existing reversible graph space extends to every
complex observable. This permits moments and conditional resolvent means to
be computed on that actual enlarged space.
-/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences

variable {X Ω : Type*} [Fintype X] [Fintype Ω]

/-- Exact event marginality implies marginality for complex observables. -/
theorem finiteExpectation_of_event_marginal (w : Ω → ℝ) (p : X → ℝ)
    (project : Ω → X)
    (hmarginal : ∀ A : X → Prop, LocalLaw.eventMass w (fun ω => A (project ω)) =
      LocalLaw.eventMass p A) (f : X → ℂ) :
    finiteExpectation w (fun ω => f (project ω)) = finiteExpectation p f := by
  classical
  have hfiber (x : X) : (∑ ω, if project ω = x then w ω else 0) = p x := by
    have h := hmarginal (fun y => y = x)
    simpa only [LocalLaw.eventMass, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h
  unfold finiteExpectation
  calc
    _ = ∑ ω, ∑ x, (if project ω = x then (w ω : ℂ) else 0) * f x := by
      apply Finset.sum_congr rfl
      intro ω _
      simp
    _ = ∑ x, (∑ ω, if project ω = x then (w ω : ℂ) else 0) * f x := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = ∑ x, (p x : ℂ) * f x := by
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      have hc := congrArg Complex.ofReal (hfiber x)
      simpa only [Complex.ofReal_sum, apply_ite, Complex.ofReal_zero] using hc

/-- Every existing reversible extension therefore has the correct complex
moments, not only the correct event probabilities. -/
theorem reversibleExtension_expectation (w : X → ℝ)
    (E : LocalLaw.ReversibleExtension X w) (f : X → ℂ) :
    finiteExpectation E.weight (fun ω => f (E.project ω)) = finiteExpectation w f :=
  finiteExpectation_of_event_marginal _ _ _ E.marginal f

/-- Exact complex conditional expectation for arbitrary dependent finite
fibers; normalization is the actual fiber size. Empty fibers are allowed. -/
theorem finiteExpectation_fiber (S : X → Type*) [∀ x, Fintype (S x)]
    (p : X → ℝ) (f : (Σ x, S x) → ℂ) :
    finiteExpectation (LocalLaw.finiteFiberWeight S p) f =
      finiteExpectation p (fun x => LocalLaw.finiteComplexMean (fun s : S x => f ⟨x,s⟩)) := by
  unfold finiteExpectation LocalLaw.finiteFiberWeight LocalLaw.finiteComplexMean
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.ofReal_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- A graph-measurable multiplier can be pulled outside the conditional
sample mean before integrating the original graph law. -/
theorem finiteExpectation_fiber_mul (S : X → Type*) [∀ x, Fintype (S x)]
    (p : X → ℝ) (f : (Σ x, S x) → ℂ) (g : X → ℂ) :
    finiteExpectation (LocalLaw.finiteFiberWeight S p) (fun ω => f ω * g ω.1) =
      finiteExpectation p (fun x =>
        LocalLaw.finiteComplexMean (fun s : S x => f ⟨x,s⟩) * g x) := by
  rw [finiteExpectation_fiber]
  congr 1
  funext x
  simp only [LocalLaw.finiteComplexMean, Complex.real_smul]
  rw [← Finset.sum_mul]
  ring

end SpectralConsequences
