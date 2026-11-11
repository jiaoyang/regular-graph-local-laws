import LocalLaw.BoundarySchurExpansion

/-!
# Boundary diagonal term and the nonlinear row remainder

An exact finite boundary sandwich splits into the correlated diagonal
observation sum and the off-diagonal error. Combined with genuine inverse
algebra, this isolates the three terms estimated in source (6.24).
-/

open scoped BigOperators
namespace LocalLaw
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] [DecidableEq I] in
/-- Exact diagonal/off-diagonal split; no probabilistic independence is used. -/
theorem boundary_sandwich_diagonal_split (U : Matrix I J ℂ) (D : Matrix J J ℂ)
    (V : Matrix J I ℂ) (i j : I) :
    (U * D * V) i j =
      (∑ a, U i a * V a j * D a a) +
      ∑ a, ∑ b ∈ (Finset.univ.erase a), U i a * D a b * V b j := by
  have hsum (a : J) : (∑ b, U i a * D a b * V b j) =
      U i a * V a j * D a a + ∑ b ∈ (Finset.univ.erase a), U i a * D a b * V b j := by
    have hh := Finset.sum_erase_add (s := Finset.univ)
      (f := fun b => U i a * D a b * V b j) (Finset.mem_univ a)
    rw [← hh]
    ring
  calc
    _ = ∑ a, ∑ b, U i a * D a b * V b j := by
      simp only [Matrix.mul_apply, Finset.sum_mul]
      exact Finset.sum_comm
    _ = ∑ a, (U i a * V a j * D a a + ∑ b ∈ (Finset.univ.erase a), U i a * D a b * V b j) :=
      Finset.sum_congr rfl (fun a _ => hsum a)
    _ = _ := Finset.sum_add_distrib

/-- Source (6.24)'s diagonal/off-diagonal/remainder decomposition is derived
from the exact inverse difference. The remaining hypotheses are its literal
self-energy factorization and physical inverse units, not error estimates. -/
theorem retained_boundary_row_three_term (R P : Matrix I I ℂ)
    (U : Matrix I J ℂ) (D : Matrix J J ℂ) (V : Matrix J I ℂ)
    (hR : IsUnit R) (hP : IsUnit P) (hW : P⁻¹ - R⁻¹ = U * D * V) (i j : I) :
    ‖R i j - P i j‖ ≤
      ‖∑ a, (P * U) i a * (V * P) a j * D a a‖ +
      ‖∑ a, ∑ b ∈ (Finset.univ.erase a), (P * U) i a * D a b * (V * P) b j‖ +
      ‖((R - P) * U * D * V * P) i j‖ := by
  have hidentity := retained_difference_expansion R P (U * D * V) hR hP hW
  have hentry := congrArg (fun A : Matrix I I ℂ => A i j) hidentity
  have hmain : P * (U * D * V) * P = (P * U) * D * (V * P) := by simp only [Matrix.mul_assoc]
  have hrem : (R - P) * (U * D * V) * P = (R - P) * U * D * V * P := by simp only [Matrix.mul_assoc]
  dsimp only at hentry
  rw [hmain, hrem, Matrix.sub_apply, Matrix.add_apply,
    boundary_sandwich_diagonal_split] at hentry
  rw [hentry]
  exact (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)

end LocalLaw
