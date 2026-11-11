import LocalLaw.GraphModel
import LocalLaw.CavityAverage
import LocalLaw.MinorIdentity

/-!
# Exact full-matrix formula and perturbation of the cavity average

One-vertex cavity resolvents are expressed through genuine full Green entries
and their proved nonzero diagonal pivots. Their rational perturbation bound
retains the three entry differences and the diagonal inverse budget explicitly.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance cavityMatrixDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The actual one-vertex Schur diagonal, written in full-matrix coordinates. -/
def matrixCavityTerm {V : Type*} (R : Matrix V V ℂ) (i j : V) : ℂ :=
  R i i - R i j * R j i / R j j

/-- A rational cavity expression has an explicit three-coordinate modulus. -/
theorem rational_cavity_difference_bound (x x' a a' b b' c c' : ℂ) (C L : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hb : ‖b‖ ≤ C) (ha' : ‖a'‖ ≤ C) (hb' : ‖b'‖ ≤ C)
    (hc : c ≠ 0) (hc' : c' ≠ 0) (hi : ‖c⁻¹‖ ≤ L) (hi' : ‖c'⁻¹‖ ≤ L) :
    ‖(x - a * b / c) - (x' - a' * b' / c')‖ ≤
      ‖x - x'‖ + C * L * (‖a - a'‖ + ‖b - b'‖) + C ^ 2 * L ^ 2 * ‖c - c'‖ := by
  have hid : c⁻¹ - c'⁻¹ = c⁻¹ * (c' - c) * c'⁻¹ := by field_simp
  have hinv : ‖c⁻¹ - c'⁻¹‖ ≤ L ^ 2 * ‖c - c'‖ := by
    rw [hid, norm_mul, norm_mul, norm_sub_rev c' c]
    calc
      _ ≤ L * ‖c - c'‖ * L := by gcongr
      _ = _ := by ring
  have h₁ : ‖(a - a') * b * c⁻¹‖ ≤ ‖a - a'‖ * C * L := by
    rw [norm_mul, norm_mul]
    gcongr
  have h₂ : ‖a' * (b - b') * c⁻¹‖ ≤ C * ‖b - b'‖ * L := by
    rw [norm_mul, norm_mul]
    gcongr
  have h₃ : ‖a' * b' * (c⁻¹ - c'⁻¹)‖ ≤ C * C * (L ^ 2 * ‖c - c'‖) := by
    rw [norm_mul, norm_mul]
    gcongr
  have heq : (x - a * b / c) - (x' - a' * b' / c') =
      (x - x') - (((a - a') * b * c⁻¹ + a' * (b - b') * c⁻¹) +
        a' * b' * (c⁻¹ - c'⁻¹)) := by rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  rw [heq]
  have hnorm := (norm_sub_le (x - x') _).trans
    (add_le_add_left ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add h₁ h₂)) h₃)) _)
  convert hnorm using 1
  ring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Schur formula identifies each actual oriented cavity entry. -/
theorem orientedCavity_eq_matrixCavityTerm (G : SimpleGraph V) (d : ℕ)
    (z : ℂ) (hz : 0 < z.im) (i j : V) :
    orientedCavity G d z i j =
      if G.Adj i j then matrixCavityTerm (green (normalizedAdjacency G d) z) i j else 0 := by
  by_cases hadj : G.Adj i j
  · simp only [orientedCavity, dif_pos hadj.ne, if_pos hadj]
    rw [green_deleted_vertex _ (normalizedAdjacency_isHermitian G d) z hz j]
    rfl
  · unfold orientedCavity
    split_ifs <;> simp_all

/-- The actual graph Q is a normalized finite sum of rational full-Green
entries. Every pivot and inverse identity has been discharged above. -/
theorem cavityAverage_eq_matrixCavityTerm (G : SimpleGraph V) (d : ℕ)
    (z : ℂ) (hz : 0 < z.im) :
    cavityAverage G d z = ((Fintype.card V : ℂ) * (d : ℂ))⁻¹ *
      ∑ i, ∑ j, if G.Adj i j then matrixCavityTerm (green (normalizedAdjacency G d) z) i j else 0 := by
  rw [cavityAverage_eq_mean]
  simp only [cavityAtVertex, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast,
    ← Finset.mul_sum, orientedCavity_eq_matrixCavityTerm G d z hz, mul_inv_rev]
  ring

omit [Fintype V] [DecidableEq V] in
/-- The matrix form of the scalar perturbation estimate. -/
theorem matrixCavityTerm_difference_bound (R S : Matrix V V ℂ) (C L : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hR : ∀ i j, ‖R i j‖ ≤ C) (hS : ∀ i j, ‖S i j‖ ≤ C)
    (hRp : ∀ j, R j j ≠ 0) (hSp : ∀ j, S j j ≠ 0)
    (hRi : ∀ j, ‖(R j j)⁻¹‖ ≤ L) (hSi : ∀ j, ‖(S j j)⁻¹‖ ≤ L) (i j : V) :
    ‖matrixCavityTerm R i j - matrixCavityTerm S i j‖ ≤
      ‖R i i - S i i‖ + C * L * (‖R i j - S i j‖ + ‖R j i - S j i‖) +
        C ^ 2 * L ^ 2 * ‖R j j - S j j‖ :=
  rational_cavity_difference_bound _ _ _ _ _ _ _ _ C L hC hL
    (hR j i) (hS i j) (hS j i) (hRp j) (hSp j) (hRi j) (hSi j)

end
end LocalLaw
