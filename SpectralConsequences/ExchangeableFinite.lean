import LocalLaw.BallResamplingMeasure

/-!
# Complex finite exchangeable-pair identities

These are the exact finite integration-by-parts identities used in Section 7.
The graph specialization uses the already proved, graph-dependent labelled
resampling law; no exchangeability or stationarity is postulated for graphs.
-/

open scoped BigOperators
noncomputable section
namespace SpectralConsequences

/-- Complex expectation for a finite real weight. -/
def finiteExpectation {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (f : Ω → ℂ) : ℂ :=
  ∑ ω, (w ω : ℂ) * f ω

variable {Ω : Type*} [Fintype Ω]

theorem finiteExpectation_add (w : Ω → ℝ) (f g : Ω → ℂ) :
    finiteExpectation w (fun ω => f ω + g ω) =
      finiteExpectation w f + finiteExpectation w g := by
  simp [finiteExpectation, mul_add, Finset.sum_add_distrib]

theorem finiteExpectation_sub (w : Ω → ℝ) (f g : Ω → ℂ) :
    finiteExpectation w (fun ω => f ω - g ω) =
      finiteExpectation w f - finiteExpectation w g := by
  simp [finiteExpectation, mul_sub, Finset.sum_sub_distrib]

theorem finiteExpectation_const_mul (w : Ω → ℝ) (a : ℂ) (f : Ω → ℂ) :
    finiteExpectation w (fun ω => a * f ω) = a * finiteExpectation w f := by
  simp only [finiteExpectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem finiteExpectation_invariant (w : Ω → ℝ) (τ : Equiv.Perm Ω)
    (hw : ∀ ω, w (τ ω) = w ω) (f : Ω → ℂ) :
    finiteExpectation w (fun ω => f (τ ω)) = finiteExpectation w f := by
  unfold finiteExpectation
  calc
    _ = ∑ ω, (w (τ ω) : ℂ) * f (τ ω) := by simp only [hw]
    _ = _ := by
      apply Fintype.sum_equiv τ
      intro ω
      rfl

/-- Antisymmetry is enough for discrete integration by parts. The factor is
exactly one half, including for complex observables and invariant cutoffs. -/
theorem exchangeable_integration_by_parts (w : Ω → ℝ) (τ : Equiv.Perm Ω)
    (hw : ∀ ω, w (τ ω) = w ω) (a f : Ω → ℂ)
    (ha : ∀ ω, a (τ ω) = -a ω) :
    finiteExpectation w (fun ω => a ω * f ω) =
      (2 : ℂ)⁻¹ * finiteExpectation w (fun ω => a ω * (f ω - f (τ ω))) := by
  have hswap := finiteExpectation_invariant w τ hw (fun ω => a ω * f ω)
  have hneg : finiteExpectation w (fun ω => a ω * f (τ ω)) =
      -finiteExpectation w (fun ω => a ω * f ω) := by
    have h : finiteExpectation w (fun ω => a (τ ω) * f (τ ω)) =
        -finiteExpectation w (fun ω => a ω * f (τ ω)) := by
      simp only [finiteExpectation, ha, neg_mul, mul_neg, Finset.sum_neg_distrib]
    rw [h] at hswap
    linear_combination -hswap
  have hdist : finiteExpectation w (fun ω => a ω * (f ω - f (τ ω))) =
      finiteExpectation w (fun ω => a ω * f ω) -
        finiteExpectation w (fun ω => a ω * f (τ ω)) := by
    simpa only [mul_sub] using finiteExpectation_sub w
      (fun ω => a ω * f ω) (fun ω => a ω * f (τ ω))
  rw [hdist, hneg]
  ring

/-- The standard difference observable is antisymmetric for an involution. -/
theorem exchangeable_difference_integration_by_parts (w : Ω → ℝ)
    (τ : Equiv.Perm Ω) (hw : ∀ ω, w (τ ω) = w ω)
    (hτ : Function.Involutive τ) (h f : Ω → ℂ) :
    finiteExpectation w (fun ω => (h ω - h (τ ω)) * f ω) =
      (2 : ℂ)⁻¹ * finiteExpectation w
        (fun ω => (h ω - h (τ ω)) * (f ω - f (τ ω))) := by
  apply exchangeable_integration_by_parts w τ hw _ f
  intro ω
  rw [hτ]
  ring

/-- Symmetric restrictions, including the event that both configurations are
regular, can be kept inside the integration-by-parts identity. -/
theorem exchangeable_cutoff_integration_by_parts (w : Ω → ℝ)
    (τ : Equiv.Perm Ω) (hw : ∀ ω, w (τ ω) = w ω)
    (hτ : Function.Involutive τ) (cut h f : Ω → ℂ)
    (hcut : ∀ ω, cut (τ ω) = cut ω) :
    finiteExpectation w (fun ω => cut ω * (h ω - h (τ ω)) * f ω) =
      (2 : ℂ)⁻¹ * finiteExpectation w
        (fun ω => cut ω * (h ω - h (τ ω)) * (f ω - f (τ ω))) := by
  apply exchangeable_integration_by_parts w τ hw _ f
  intro ω
  rw [hcut, hτ]
  ring

/-- Genuine graph-specific exchangeability for radius-ell local resampling.
All weight and involution hypotheses are discharged by the source construction. -/
theorem ball_resampling_integration_by_parts (N d : ℕ) (o : Fin N)
    (ell selector : ℕ) (h f : LocalLaw.BallLabelledSpace N d → ℂ) :
    finiteExpectation (LocalLaw.ballLabelledWeight N d o ell)
      (fun ω => (h ω - h (LocalLaw.ballLabelledPermutation N d selector ω)) * f ω) =
      (2 : ℂ)⁻¹ * finiteExpectation (LocalLaw.ballLabelledWeight N d o ell)
        (fun ω => (h ω - h (LocalLaw.ballLabelledPermutation N d selector ω)) *
          (f ω - f (LocalLaw.ballLabelledPermutation N d selector ω))) := by
  exact exchangeable_difference_integration_by_parts _ _
    (LocalLaw.ballLabelledWeight_preserved N d o ell selector)
    (LocalLaw.ballLabelledResample_involutive N d selector) h f

end SpectralConsequences
