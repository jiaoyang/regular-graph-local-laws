import LocalLaw.BoundaryRowBootstrap
import LocalLaw.SourceBoundaryExpansion

/-!
# Exact cut normalization and the finite nonlinear row contraction

The physical cut incidence selects one actual retained endpoint per label.
This identifies the boundary weights and turns the exact retained Schur
expansion into the derived boundary-error-sum contraction.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance cutRowAlgebraDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

def cutInsideVertex (G : SimpleGraph V) (T : Set V) (a : BoundaryOrientedEdge G T) : T :=
  ⟨a.val.1, a.property.2.1⟩

theorem mul_cutInnerCoupling {I : Type*} (G : SimpleGraph V) (d : ℕ) (T : Set V)
    (A : Matrix I T ℂ) (i : I) (a : BoundaryOrientedEdge G T) :
    (A * cutInnerCoupling G d T) i a =
      (↑((Real.sqrt ((d : ℝ) - 1))⁻¹) : ℂ) * A i (cutInsideVertex G T a) := by
  change (∑ j : T, A i j * (if j.val = a.val.1 then _ else 0)) = _
  have hpred (j : T) : (j.val = a.val.1) ↔ j = cutInsideVertex G T a :=
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  simp only [hpred, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem transpose_cutInnerCoupling_mul {J : Type*} (G : SimpleGraph V) (d : ℕ) (T : Set V)
    (B : Matrix T J ℂ) (a : BoundaryOrientedEdge G T) (j : J) :
    ((cutInnerCoupling G d T).transpose * B) a j =
      (↑((Real.sqrt ((d : ℝ) - 1))⁻¹) : ℂ) * B (cutInsideVertex G T a) j := by
  change (∑ i : T, (if i.val = a.val.1 then _ else 0) * B i j) = _
  have hpred (i : T) : (i.val = a.val.1) ↔ i = cutInsideVertex G T a :=
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  simp only [hpred, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Exact normalized source boundary sum, allowing repeated endpoints. -/
theorem cut_sandwich_row_formula {I J : Type*} (G : SimpleGraph V) (d : ℕ) (T : Set V)
    (A : Matrix I T ℂ) (D : Matrix (BoundaryOrientedEdge G T) (BoundaryOrientedEdge G T) ℂ)
    (B : Matrix T J ℂ) (i : I) (j : J) :
    ((A * cutInnerCoupling G d T) * D * ((cutInnerCoupling G d T).transpose * B)) i j =
      (↑((Real.sqrt ((d : ℝ) - 1))⁻¹) : ℂ) ^ 2 *
        ∑ a, ∑ b, A i (cutInsideVertex G T a) * D a b * B (cutInsideVertex G T b) j := by
  calc
    _ = ∑ a, ∑ b, (A * cutInnerCoupling G d T) i a * D a b *
        ((cutInnerCoupling G d T).transpose * B) b j := by
      simp only [Matrix.mul_apply, Finset.sum_mul]
      exact Finset.sum_comm
    _ = _ := by
      simp only [mul_cutInnerCoupling, transpose_cutInnerCoupling_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

/-- The squared physical edge normalization has norm at most one. -/
theorem cut_coefficient_norm_le_one (d : ℕ) (hd : 3 ≤ d) :
    ‖(↑((Real.sqrt ((d : ℝ) - 1))⁻¹) : ℂ) ^ 2‖ ≤ 1 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ Real.sqrt ((d : ℝ) - 1) := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt (show 0 ≤ (d : ℝ) - 1 by linarith)
  have hs : 1 ≤ Real.sqrt ((d : ℝ) - 1) := by nlinarith
  have hi : (Real.sqrt ((d : ℝ) - 1))⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr hs
  have hn : ‖(↑((Real.sqrt ((d : ℝ) - 1))⁻¹) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hs0)]
    exact hi
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) hn

/-- The boundary-error sum and nonlinear remainder follow from the literal
cut Schur identity and column estimates; neither is assumed. -/
theorem cut_boundary_row_error_and_remainder (G : SimpleGraph V) (d : ℕ) (hd : 3 ≤ d) (T : Set V)
    (R P : Matrix T T ℂ) (D : Matrix (BoundaryOrientedEdge G T) (BoundaryOrientedEdge G T) ℂ)
    (i : T) (M e S : ℝ) (hM : 0 ≤ M) (he : 0 ≤ e) (hS : 0 ≤ S)
    (hroot : ∀ a, ‖P i (cutInsideVertex G T a)‖ ≤ M)
    (hD : ∀ b, (∑ a, ‖D a b‖) ≤ e)
    (hP : ∀ j, (∑ b, ‖P (cutInsideVertex G T b) j‖) ≤ S)
    (hidentity : R - P = (P * cutInnerCoupling G d T) * D * ((cutInnerCoupling G d T).transpose * P) +
      (R - P) * cutInnerCoupling G d T * D * (cutInnerCoupling G d T).transpose * P)
    (hsmall : (Fintype.card (BoundaryOrientedEdge G T) : ℝ) * e * S ≤ 1 / 2) :
    (∑ a, ‖R i (cutInsideVertex G T a) - P i (cutInsideVertex G T a)‖) ≤
        2 * (Fintype.card (BoundaryOrientedEdge G T) : ℝ) * M * e * S ∧
      ∀ j, ‖((R - P) * cutInnerCoupling G d T * D * (cutInnerCoupling G d T).transpose * P) i j‖ ≤
        2 * (Fintype.card (BoundaryOrientedEdge G T) : ℝ) * M * e ^ 2 * S ^ 2 := by
  let c : ℂ := (↑((Real.sqrt ((d : ℝ) - 1))⁻¹) : ℂ) ^ 2
  have hrow (j : T) : R i j - P i j =
      c * (∑ a, ∑ b, P i (cutInsideVertex G T a) * D a b * P (cutInsideVertex G T b) j) +
      c * (∑ a, ∑ b, (R i (cutInsideVertex G T a) - P i (cutInsideVertex G T a)) *
        D a b * P (cutInsideVertex G T b) j) := by
    have hh := congrArg (fun A : Matrix T T ℂ => A i j) hidentity
    dsimp only at hh
    rw [Matrix.sub_apply, Matrix.add_apply, cut_sandwich_row_formula] at hh
    have hrem : (R - P) * cutInnerCoupling G d T * D * (cutInnerCoupling G d T).transpose * P =
        ((R - P) * cutInnerCoupling G d T) * D * ((cutInnerCoupling G d T).transpose * P) := by
      simp only [Matrix.mul_assoc]
    rw [hrem, cut_sandwich_row_formula] at hh
    exact hh
  have hh := boundary_row_error_sum_and_remainder R P (cutInsideVertex G T) D c i M e S
    hM he hS (cut_coefficient_norm_le_one d hd) hroot hD hP hrow hsmall
  refine ⟨hh.1, ?_⟩
  intro j
  have hrem : (R - P) * cutInnerCoupling G d T * D * (cutInnerCoupling G d T).transpose * P =
      ((R - P) * cutInnerCoupling G d T) * D * ((cutInnerCoupling G d T).transpose * P) := by
    simp only [Matrix.mul_assoc]
  rw [hrem, cut_sandwich_row_formula]
  exact hh.2 j

end
end LocalLaw
