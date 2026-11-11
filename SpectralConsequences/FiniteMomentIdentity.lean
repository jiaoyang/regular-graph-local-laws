import SpectralConsequences.ExchangeableFinite
import SpectralConsequences.ComplexMomentAlgebra

/-! # Exact truncated high-moment identity for a finite exchangeable pair

The two error terms have different roles: conditional drift and exit from the
regularity event. The exit term is explicit and cannot be discarded by
exchangeability. No high-moment estimate is assumed or concluded here.
-/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences

variable {Ω : Type*} [Fintype Ω]

/-- Actual unnormalized moment on an event. -/
def truncatedMoment (w : Ω → ℝ) (A : Ω → Prop) [DecidablePred A]
    (F : Ω → ℂ) (p : ℕ) : ℝ :=
  ∑ ω, if A ω then w ω * ‖F ω‖^(2*p) else 0

theorem truncatedMoment_nonnegative (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (A : Ω → Prop) [DecidablePred A] (F : Ω → ℂ) (p : ℕ) :
    0 ≤ truncatedMoment w A F p := by
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact mul_nonneg (hw ω) (pow_nonneg (norm_nonneg _) _)
  · exact le_rfl

theorem truncatedMoment_complex_energy (w : Ω → ℝ)
    (A : Ω → Prop) [DecidablePred A] (F : Ω → ℂ) (p : ℕ) (hp : 1 ≤ p) :
    (truncatedMoment w A F p : ℂ) =
      finiteExpectation w (fun ω => if A ω then F ω*complexMomentTest p (F ω) else 0) := by
  unfold truncatedMoment finiteExpectation
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hA : A ω
  · simp only [hA,if_true,complexMomentTest_energy p hp,Complex.ofReal_mul]
  · simp only [hA,if_false,Complex.ofReal_zero,mul_zero]

/-- The exact Section 7 split into conditional drift, symmetric integration
by parts, and event exit. In particular event exit is not charged only once
per ordered vertex pair; its actual expectation remains visible. -/
theorem truncated_exchangeable_moment_identity (w : Ω → ℝ)
    (τ : Equiv.Perm Ω) (hw : ∀ ω, w (τ ω) = w ω)
    (hτ : Function.Involutive τ) (A : Ω → Prop) [DecidablePred A]
    (h target F : Ω → ℂ) (hF : ∀ ω, F ω = h ω-target ω)
    (p : ℕ) (hp : 1 ≤ p) :
    (truncatedMoment w A F p : ℂ) =
      finiteExpectation w (fun ω => if A ω then
        (h (τ ω)-target ω)*complexMomentTest p (F ω) else 0) +
      (2 : ℂ)⁻¹ * finiteExpectation w (fun ω => if A ω ∧ A (τ ω) then
        (h ω-h (τ ω)) *
          (complexMomentTest p (F ω)-complexMomentTest p (F (τ ω))) else 0) +
      finiteExpectation w (fun ω => if A ω ∧ ¬A (τ ω) then
        (h ω-h (τ ω))*complexMomentTest p (F ω) else 0) := by
  classical
  let cut : Ω → ℂ := fun ω => if A ω ∧ A (τ ω) then 1 else 0
  have hcut : ∀ ω, cut (τ ω) = cut ω := by
    intro ω
    dsimp only [cut]
    simp only [hτ ω]
    by_cases ha : A ω <;> by_cases hb : A (τ ω) <;> simp [ha,hb]
  have hibp := exchangeable_cutoff_integration_by_parts w τ hw hτ cut h
    (fun ω => complexMomentTest p (F ω)) hcut
  have hpart : finiteExpectation w (fun ω => if A ω ∧ A (τ ω) then
      (h ω-h (τ ω))*complexMomentTest p (F ω) else 0) =
      (2 : ℂ)⁻¹ * finiteExpectation w (fun ω => if A ω ∧ A (τ ω) then
        (h ω-h (τ ω)) *
          (complexMomentTest p (F ω)-complexMomentTest p (F (τ ω))) else 0) := by
    simpa only [cut, ite_mul, one_mul, zero_mul] using hibp
  rw [truncatedMoment_complex_energy w A F p hp]
  have hsplit : finiteExpectation w (fun ω => if A ω then
      F ω*complexMomentTest p (F ω) else 0) =
      finiteExpectation w (fun ω => if A ω then
        (h (τ ω)-target ω)*complexMomentTest p (F ω) else 0) +
      finiteExpectation w (fun ω => if A ω ∧ A (τ ω) then
        (h ω-h (τ ω))*complexMomentTest p (F ω) else 0) +
      finiteExpectation w (fun ω => if A ω ∧ ¬A (τ ω) then
        (h ω-h (τ ω))*complexMomentTest p (F ω) else 0) := by
    rw [← finiteExpectation_add, ← finiteExpectation_add]
    congr 1
    funext ω
    by_cases ha : A ω <;> by_cases hb : A (τ ω) <;>
      simp only [ha,hb,not_true_eq_false,not_false_eq_true,and_self,and_false,
        and_true,false_and,if_true,if_false,hF] <;> ring
  rw [hsplit,hpart]

end SpectralConsequences
