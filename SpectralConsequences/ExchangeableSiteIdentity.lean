import SpectralConsequences.FiniteExpectationMarginal

/-! # Local-observable identity on a graph-dependent reversible extension

Each graph center may have a different enlarged sample space. The identity
keeps this dependence and does not introduce a common sampling space.
-/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences

variable {Ω : Type*} [Fintype Ω]

/-- Exact drift/symmetric-increment/exit decomposition for an arbitrary test.
The local observable need not equal the global residual. -/
theorem exchangeable_test_identity (w : Ω → ℝ)
    (τ : Equiv.Perm Ω) (hw : ∀ ω, w (τ ω) = w ω)
    (hτ : Function.Involutive τ) (A : Ω → Prop) [DecidablePred A]
    (h target test : Ω → ℂ) :
    finiteExpectation w (fun ω => if A ω then (h ω-target ω)*test ω else 0) =
      finiteExpectation w (fun ω => if A ω then (h (τ ω)-target ω)*test ω else 0) +
      (2 : ℂ)⁻¹ * finiteExpectation w (fun ω => if A ω ∧ A (τ ω) then
        (h ω-h (τ ω))*(test ω-test (τ ω)) else 0) +
      finiteExpectation w (fun ω => if A ω ∧ ¬A (τ ω) then
        (h ω-h (τ ω))*test ω else 0) := by
  classical
  let cut : Ω → ℂ := fun ω => if A ω ∧ A (τ ω) then 1 else 0
  have hcut : ∀ ω, cut (τ ω) = cut ω := by
    intro ω
    dsimp only [cut]
    simp only [hτ ω]
    by_cases ha : A ω <;> by_cases hb : A (τ ω) <;> simp [ha,hb]
  have hibp := exchangeable_cutoff_integration_by_parts w τ hw hτ cut h test hcut
  have hpart : finiteExpectation w (fun ω => if A ω ∧ A (τ ω) then
      (h ω-h (τ ω))*test ω else 0) =
      (2 : ℂ)⁻¹ * finiteExpectation w (fun ω => if A ω ∧ A (τ ω) then
        (h ω-h (τ ω))*(test ω-test (τ ω)) else 0) := by
    simpa only [cut,ite_mul,one_mul,zero_mul] using hibp
  have hsplit : finiteExpectation w (fun ω => if A ω then
      (h ω-target ω)*test ω else 0) =
      finiteExpectation w (fun ω => if A ω then (h (τ ω)-target ω)*test ω else 0) +
      finiteExpectation w (fun ω => if A ω ∧ A (τ ω) then
        (h ω-h (τ ω))*test ω else 0) +
      finiteExpectation w (fun ω => if A ω ∧ ¬A (τ ω) then
        (h ω-h (τ ω))*test ω else 0) := by
    rw [← finiteExpectation_add,← finiteExpectation_add]
    congr 1
    funext ω
    by_cases ha : A ω <;> by_cases hb : A (τ ω) <;>
      simp only [ha,hb,not_true_eq_false,not_false_eq_true,and_self,and_false,
        and_true,false_and,if_true,if_false] <;> ring
  rw [hsplit,hpart]

/-- The corresponding local identity on the original graph law. Every
marginal, involution and measure-preservation fact comes from its actual
reversible extension. -/
theorem reversible_site_test_identity {X : Type*} [Fintype X] (w : X → ℝ)
    (E : LocalLaw.ReversibleExtension X w) (A : X → Prop) [DecidablePred A]
    (h target test : X → ℂ) :
    finiteExpectation w (fun x => if A x then (h x-target x)*test x else 0) =
      finiteExpectation E.weight (fun ω => if A (E.project ω) then
        (h (E.project (E.switching ω))-target (E.project ω))*test (E.project ω) else 0) +
      (2 : ℂ)⁻¹ * finiteExpectation E.weight (fun ω =>
        if A (E.project ω) ∧ A (E.project (E.switching ω)) then
          (h (E.project ω)-h (E.project (E.switching ω)))*
            (test (E.project ω)-test (E.project (E.switching ω))) else 0) +
      finiteExpectation E.weight (fun ω =>
        if A (E.project ω) ∧ ¬A (E.project (E.switching ω)) then
          (h (E.project ω)-h (E.project (E.switching ω)))*test (E.project ω) else 0) := by
  rw [← reversibleExtension_expectation w E
    (fun x => if A x then (h x-target x)*test x else 0)]
  exact exchangeable_test_identity E.weight E.switching E.preserve E.involution
    (fun ω => A (E.project ω)) (fun ω => h (E.project ω))
    (fun ω => target (E.project ω)) (fun ω => test (E.project ω))

end SpectralConsequences
