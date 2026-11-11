import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.Data.Fin.Tuple.Sort

/-! # A descending Hermitian spectrum with its multiplicities retained

Sorting reindexes the actual orthonormal eigenbasis by a permutation. No
eigenvalue is removed when several eigenvalues have the same value.
-/

open scoped BigOperators
open Matrix
noncomputable section
namespace SpectralConsequences
variable {N : ℕ} {H : Matrix (Fin N) (Fin N) ℂ}

/-- The permutation orders the supplied eigenvalues in decreasing order. -/
def sortedEigenvaluePermutation (hH : H.IsHermitian) : Equiv.Perm (Fin N) :=
  Tuple.sort (fun i => OrderDual.toDual (hH.eigenvalues i))

/-- The actual eigenvalues, in decreasing order and with multiplicities. -/
def sortedEigenvalues (hH : H.IsHermitian) : Fin N → ℝ :=
  fun i => hH.eigenvalues (sortedEigenvaluePermutation hH i)

theorem sortedEigenvalues_antitone (hH : H.IsHermitian) :
    Antitone (sortedEigenvalues hH) := by
  exact Tuple.monotone_sort (fun i => OrderDual.toDual (hH.eigenvalues i))

/-- The corresponding permuted orthonormal eigenbasis. -/
def sortedEigenbasis (hH : H.IsHermitian) :
    OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)) :=
  hH.eigenvectorBasis.reindex (sortedEigenvaluePermutation hH).symm

theorem mulVec_sortedEigenbasis (hH : H.IsHermitian) (i : Fin N) :
    H *ᵥ (⇑(sortedEigenbasis hH i)) =
      (sortedEigenvalues hH i) • ⇑(sortedEigenbasis hH i) := by
  simpa only [sortedEigenbasis, sortedEigenvalues, OrthonormalBasis.reindex_apply,
    Equiv.symm_symm] using hH.mulVec_eigenvectorBasis (sortedEigenvaluePermutation hH i)

/-- Every additive statistic of the indexed eigenvalue list is unchanged. -/
theorem sum_sortedEigenvalues (hH : H.IsHermitian) {A : Type*} [AddCommMonoid A]
    (f : ℝ → A) :
    (∑ i, f (sortedEigenvalues hH i)) = ∑ i, f (hH.eigenvalues i) := by
  exact Equiv.sum_comp (sortedEigenvaluePermutation hH) (fun i => f (hH.eigenvalues i))

/-- Sorting retains the exact number of indices satisfying any predicate. -/
theorem card_sortedEigenvalues (hH : H.IsHermitian) (P : ℝ → Prop) :
    Nat.card {i // P (sortedEigenvalues hH i)} = Nat.card {i // P (hH.eigenvalues i)} := by
  exact Nat.card_congr ((sortedEigenvaluePermutation hH).subtypeEquiv (fun _ => Iff.rfl))

end SpectralConsequences
