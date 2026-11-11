import LocalLaw.FullQuadVacuumBenchmark

/-! # Proof-independent decidable equality in full switching matrices -/

noncomputable section
namespace LocalLaw

theorem fullQuadSurgeryCoupling_decidableCongr {K I : Type} [Fintype I]
    (dk dk' : DecidableEq K) (di di' : DecidableEq I)
    (inner outer : I → Option K) (B C : Set I) (q α : ℂ) :
    @fullQuadSurgeryCoupling K I _ dk di inner outer B C q α =
      @fullQuadSurgeryCoupling K I _ dk' di' inner outer B C q α := by
  cases Subsingleton.elim dk dk'
  cases Subsingleton.elim di di'
  rfl

end LocalLaw
