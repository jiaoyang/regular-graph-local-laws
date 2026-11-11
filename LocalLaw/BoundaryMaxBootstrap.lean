import LocalLaw.CutRowAlgebra

/-!
# Boundary maximum contraction for quadratic-log exceptional sets

Unlike a sum bootstrap, the finite maximum costs no extra boundary-label
factor in the contraction or remainder. Both bounds follow from the exact
Schur row identity, including the empty-boundary case.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance boundaryMaxBootstrapDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {I F : Type*} [Fintype F]

theorem boundary_row_max_and_remainder
    (R P : Matrix I I ℂ) (l : F → I) (D : Matrix F F ℂ) (c : ℂ) (i : I)
    (M e S : ℝ) (hM : 0 ≤ M) (he : 0 ≤ e) (hS : 0 ≤ S) (hc : ‖c‖ ≤ 1)
    (hroot : ∀ a, ‖P i (l a)‖ ≤ M)
    (hD : ∀ b, (∑ a, ‖D a b‖) ≤ e)
    (hP : ∀ j, (∑ b, ‖P (l b) j‖) ≤ S)
    (hidentity : ∀ j,
      R i j - P i j = c * (∑ a, ∑ b, P i (l a) * D a b * P (l b) j) +
        c * (∑ a, ∑ b, (R i (l a) - P i (l a)) * D a b * P (l b) j))
    (hsmall : e * S ≤ 1 / 2) :
    (∀ a, ‖R i (l a) - P i (l a)‖ ≤ 2 * M * e * S) ∧
      ∀ j, ‖c * (∑ a, ∑ b, (R i (l a) - P i (l a)) * D a b * P (l b) j)‖ ≤
        2 * M * e ^ 2 * S ^ 2 := by
  rcases isEmpty_or_nonempty F with hF | hF
  · letI : IsEmpty F := hF
    constructor
    · intro a; exact isEmptyElim a
    · intro j; simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, norm_zero]; positivity
  · letI : Nonempty F := hF
    let Γ : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun a => ‖R i (l a) - P i (l a)‖)
    have hpoint (a : F) : ‖R i (l a) - P i (l a)‖ ≤ Γ := Finset.le_sup' (fun a => ‖R i (l a) - P i (l a)‖) (Finset.mem_univ a)
    have hΓ : 0 ≤ Γ := (norm_nonneg _).trans (hpoint (Classical.choice hF))
    have hlead (j : I) : ‖c * (∑ a, ∑ b, P i (l a) * D a b * P (l b) j)‖ ≤ M * e * S := by
      rw [norm_mul]
      have hh := boundary_double_sum_bound (fun a => P i (l a)) D (fun b => P (l b) j)
        M e S hM he hroot hD (hP j)
      exact (mul_le_mul_of_nonneg_left hh (norm_nonneg c)).trans (mul_le_of_le_one_left (by positivity) hc)
    have hrem (j : I) : ‖c * (∑ a, ∑ b, (R i (l a) - P i (l a)) * D a b * P (l b) j)‖ ≤ Γ * e * S := by
      rw [norm_mul]
      have hh := boundary_double_sum_bound (fun a => R i (l a) - P i (l a)) D (fun b => P (l b) j)
        Γ e S hΓ he hpoint hD (hP j)
      exact (mul_le_mul_of_nonneg_left hh (norm_nonneg c)).trans (mul_le_of_le_one_left (by positivity) hc)
    have hbound (j : I) : ‖R i j - P i j‖ ≤ (M + Γ) * e * S := by
      rw [hidentity j]
      exact ((norm_add_le _ _).trans (add_le_add (hlead j) (hrem j))).trans_eq (by ring)
    have hmax : Γ ≤ (M + Γ) * e * S :=
      Finset.sup'_le Finset.univ_nonempty (fun a => ‖R i (l a) - P i (l a)‖) (fun a _ => hbound (l a))
    have hcontract : e * S * Γ ≤ Γ / 2 := by
      have hh := mul_le_mul_of_nonneg_right hsmall hΓ
      exact hh.trans_eq (by ring)
    have hΓbound : Γ ≤ 2 * M * e * S := by nlinarith only [hmax, hcontract]
    refine ⟨fun a => (hpoint a).trans hΓbound, ?_⟩
    intro j
    exact (hrem j).trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hΓbound he) hS).trans_eq (by ring))

section Cut
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The physical cut form has all normalization and endpoint selection
proved, so the maximum bootstrap applies directly to the actual row expansion. -/
theorem cut_boundary_max_and_remainder (G : SimpleGraph V) (d : ℕ) (hd : 3 ≤ d) (T : Set V)
    (R P : Matrix T T ℂ) (D : Matrix (BoundaryOrientedEdge G T) (BoundaryOrientedEdge G T) ℂ)
    (i : T) (M e S : ℝ) (hM : 0 ≤ M) (he : 0 ≤ e) (hS : 0 ≤ S)
    (hroot : ∀ a, ‖P i (cutInsideVertex G T a)‖ ≤ M)
    (hD : ∀ b, (∑ a, ‖D a b‖) ≤ e)
    (hP : ∀ j, (∑ b, ‖P (cutInsideVertex G T b) j‖) ≤ S)
    (hidentity : R - P = (P * cutInnerCoupling G d T) * D * ((cutInnerCoupling G d T).transpose * P) +
      (R - P) * cutInnerCoupling G d T * D * (cutInnerCoupling G d T).transpose * P)
    (hsmall : e * S ≤ 1 / 2) :
    (∀ a, ‖R i (cutInsideVertex G T a) - P i (cutInsideVertex G T a)‖ ≤ 2 * M * e * S) ∧
      ∀ j, ‖((R - P) * cutInnerCoupling G d T * D * (cutInnerCoupling G d T).transpose * P) i j‖ ≤
        2 * M * e ^ 2 * S ^ 2 := by
  let c : ℂ := (↑((Real.sqrt ((d : ℝ) - 1))⁻¹) : ℂ) ^ 2
  have hrow (j : T) : R i j - P i j =
      c * (∑ a, ∑ b, P i (cutInsideVertex G T a) * D a b * P (cutInsideVertex G T b) j) +
      c * (∑ a, ∑ b, (R i (cutInsideVertex G T a) - P i (cutInsideVertex G T a)) * D a b * P (cutInsideVertex G T b) j) := by
    have hh := congrArg (fun A : Matrix T T ℂ => A i j) hidentity
    dsimp only at hh
    rw [Matrix.sub_apply, Matrix.add_apply, cut_sandwich_row_formula] at hh
    have hrem : (R - P) * cutInnerCoupling G d T * D * (cutInnerCoupling G d T).transpose * P =
        ((R - P) * cutInnerCoupling G d T) * D * ((cutInnerCoupling G d T).transpose * P) := by simp only [Matrix.mul_assoc]
    rw [hrem, cut_sandwich_row_formula] at hh
    exact hh
  have hh := boundary_row_max_and_remainder R P (cutInsideVertex G T) D c i M e S hM he hS
    (cut_coefficient_norm_le_one d hd) hroot hD hP hrow hsmall
  refine ⟨hh.1, ?_⟩
  intro j
  have hrem : (R - P) * cutInnerCoupling G d T * D * (cutInnerCoupling G d T).transpose * P =
      ((R - P) * cutInnerCoupling G d T) * D * ((cutInnerCoupling G d T).transpose * P) := by simp only [Matrix.mul_assoc]
  rw [hrem, cut_sandwich_row_formula]
  exact hh.2 j

end Cut
end LocalLaw
