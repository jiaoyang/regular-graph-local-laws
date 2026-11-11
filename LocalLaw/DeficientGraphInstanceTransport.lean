import LocalLaw.DeficientGraphModel

/-! # Proof-instance independence of the actual finite model matrices

Concrete subtype and sum indices may synthesize different equality
deciders. The matrices and their genuine inverses are unchanged.
-/

noncomputable section
namespace LocalLaw.DeficientGraph
variable {V : Type*}[Fintype V]{d : ℕ}

theorem extensionMatrix_decidableEq_eq (g : DeficientGraph V d)(a b : DecidableEq V)(q z : ℂ) :
    @extensionMatrix V _ a d g q z = @extensionMatrix V _ b d g q z := by
  cases Subsingleton.elim a b
  rfl

theorem extensionGreen_decidableEq_eq (g : DeficientGraph V d)(a b : DecidableEq V)(q z : ℂ) :
    @extensionGreen V _ a d g q z = @extensionGreen V _ b d g q z := by
  cases Subsingleton.elim a b
  rfl

end LocalLaw.DeficientGraph
