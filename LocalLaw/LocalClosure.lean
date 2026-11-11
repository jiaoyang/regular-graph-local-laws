import LocalLaw.ScalarRecursion
import LocalLaw.ScalarStability
import LocalLaw.Abstract

/-!
# Deterministic closure from local cavity certificates

This module connects the exact cavity recurrence to quadratic stability and
then derives the strict half-sized bootstrap budgets. Local graph estimates
are explicit inputs. Exceptional centers are retained in the averaging error.
-/

open scoped BigOperators

namespace LocalLaw

/-- The scalar improvement constant after converting a cavity residual on a
spectral region of radius `B` to a polynomial residual. -/
noncomputable def localClosureConstant (B G : ℝ) : ℝ :=
  scalarConstant G (3 * (B + 1))

/-- Local recurrence and row certificates imply the strict event required
by the probabilistic bootstrap. In particular, the final tightening is proved,
not supplied as a hypothesis. `rowError` may encode all entrywise errors. -/
theorem local_certificate_closure {I : Type*}
    (q m z : ℂ) (n : ℕ) (s ε L K G B U V u v : ℝ) (rowError : I → ℝ)
    (hm : m ^ 2 + z * m + 1 = 0) (hmnorm : ‖m‖ ≤ 1) (hz : ‖z‖ ≤ B)
    (hsmall : (n : ℝ) * ‖q - m‖ ≤ 1 / 2)
    (hnonresonant : 1 / 2 ≤ ‖cavitySum m n‖)
    (hs : 0 < s) (hε : 0 < ε) (hK : 0 ≤ K) (hG : 0 ≤ G)
    (_hU : 0 ≤ U) (hV : 0 ≤ V)
    (hL : 2 ≤ L) (hLK : 2 * K ≤ L)
    (hgap₁ : Real.sqrt s ≤ ‖m⁻¹ - m‖)
    (hgap₂ : ‖m⁻¹ - m‖ ≤ G * Real.sqrt s)
    (hprior : ‖q - m‖ ≤ K * scalarScale s ε)
    (hresidual : ‖q - cavityIterate z q n‖ ≤ ε / L ^ 2)
    (hregime : ε ≤ s / L ∨ L ^ 3 * s ≤ ε)
    (hrow : ∀ i, rowError i ≤
      u + v * (Real.sqrt s * ‖q - m‖ + ‖q - m‖ ^ 2))
    (hu : u ≤ U * ε / L) (hv : v ≤ V * L)
    (hLscalar : 2 * localClosureConstant B G ≤ L)
    (hLrow : 2 * (U + V *
      (localClosureConstant B G + localClosureConstant B G ^ 2)) ≤ L) :
    ‖q - m‖ ≤ scalarScale s ε / 2 ∧ ∀ i, rowError i ≤ ε / 2 := by
  let M := 3 * (B + 1)
  let C := localClosureConstant B G
  have hB : 0 ≤ B := (norm_nonneg z).trans hz
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hLp : 0 < L := by linarith
  have hC : 0 ≤ C := by
    dsimp [C, localClosureConstant]
    linarith [scalarConstant_one_le G M]
  have hpoly : ‖(q - m) * ((q - m) - (m⁻¹ - m))‖ ≤ M * ε / L ^ 2 := by
    rw [← cavity_quadratic_factor hm]
    calc
      ‖q ^ 2 + z * q + 1‖ ≤ M * ‖q - cavityIterate z q n‖ :=
        cavity_polynomial_residual_bound_bounded hm hmnorm n hsmall hnonresonant hz
      _ ≤ M * (ε / L ^ 2) := mul_le_mul_of_nonneg_left hresidual hM
      _ = M * ε / L ^ 2 := by ring
  have hscalar := scalar_two_regime (q - m) (m⁻¹ - m) s ε L K G M
    hs hε hK hG hM hL hLK hgap₁ hgap₂ hprior hpoly hregime
  have hnorm : ‖q - m‖ ≤ C * scalarScale s ε / L := hscalar.1
  have hfeedback : L * (Real.sqrt s * ‖q - m‖ + ‖q - m‖ ^ 2) ≤
      (C + C ^ 2) * ε / L := hscalar.2
  have hhalfscalar : C * scalarScale s ε / L ≤ scalarScale s ε / 2 := by
    apply (div_le_iff₀ hLp).2
    have hΨ := scalarScale_nonneg (s := s) hε.le
    have hlarge := mul_le_mul_of_nonneg_right hLscalar hΨ
    change 2 * C * scalarScale s ε ≤ L * scalarScale s ε at hlarge
    nlinarith
  refine ⟨hnorm.trans hhalfscalar, ?_⟩
  intro i
  have hfeedback_nonneg : 0 ≤ Real.sqrt s * ‖q - m‖ + ‖q - m‖ ^ 2 := by
    positivity
  have hrowbound : rowError i ≤ (U + V * (C + C ^ 2)) * ε / L := by
    calc
      rowError i ≤ u + v * (Real.sqrt s * ‖q - m‖ + ‖q - m‖ ^ 2) := hrow i
      _ ≤ U * ε / L + (V * L) *
          (Real.sqrt s * ‖q - m‖ + ‖q - m‖ ^ 2) :=
        add_le_add hu (mul_le_mul_of_nonneg_right hv hfeedback_nonneg)
      _ = U * ε / L + V *
          (L * (Real.sqrt s * ‖q - m‖ + ‖q - m‖ ^ 2)) := by ring
      _ ≤ U * ε / L + V * ((C + C ^ 2) * ε / L) :=
        add_le_add_left (mul_le_mul_of_nonneg_left hfeedback hV) _
      _ = (U + V * (C + C ^ 2)) * ε / L := by ring
  apply hrowbound.trans
  apply (div_le_iff₀ hLp).2
  have hlarge := mul_le_mul_of_nonneg_right hLrow hε.le
  change 2 * (U + V * (C + C ^ 2)) * ε ≤ L * ε at hlarge
  nlinarith

/-- Averaging local cavity certificates retains the exceptional-center
contribution explicitly. The input `cavity` is the neighbor-averaged cavity
value at each center. -/
theorem averaged_cavity_residual {J : Type*} [Fintype J] [DecidableEq J]
    (cavity : J → ℂ) (q y : ℂ) (bad : Finset J) (t M₀ : ℝ)
    (hcard : 0 < Fintype.card J) (ht : 0 ≤ t)
    (hq : q = (Fintype.card J : ℝ)⁻¹ • ∑ i, cavity i)
    (hgood : ∀ i, i ∉ bad → ‖cavity i - y‖ ≤ t)
    (hbad : ∀ i, i ∈ bad → ‖cavity i - y‖ ≤ M₀) :
    ‖q - y‖ ≤ t + ((bad.card : ℝ) / (Fintype.card J : ℝ)) * M₀ := by
  have hN : (Fintype.card J : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hcard)
  have hconst : (Fintype.card J : ℝ)⁻¹ • (∑ _i : J, y) = y := by
    simp only [Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hN, one_smul]
  have hmean : (Fintype.card J : ℝ)⁻¹ • (∑ i, (cavity i - y)) = q - y := by
    rw [Finset.sum_sub_distrib, smul_sub, ← hq, hconst]
  rw [← hmean]
  apply sparse_average_bound (fun i => cavity i - y) bad t M₀ hcard hgood
  intro i hi
  exact (hbad i hi).trans (by linarith)

/-- Local good-center certificates and a sparse exceptional set imply the
small averaged residual used by `local_certificate_closure`. -/
theorem cavity_certificate_residual {J : Type*} [Fintype J] [DecidableEq J]
    (cavity : J → ℂ) (q z : ℂ) (n : ℕ) (bad : Finset J)
    (t M₀ ε L : ℝ) (hcard : 0 < Fintype.card J) (ht : 0 ≤ t)
    (hq : q = (Fintype.card J : ℝ)⁻¹ • ∑ i, cavity i)
    (hgood : ∀ i, i ∉ bad → ‖cavity i - cavityIterate z q n‖ ≤ t)
    (hbad : ∀ i, i ∈ bad → ‖cavity i - cavityIterate z q n‖ ≤ M₀)
    (hbudget : t + ((bad.card : ℝ) / (Fintype.card J : ℝ)) * M₀ ≤ ε / L ^ 2) :
    ‖q - cavityIterate z q n‖ ≤ ε / L ^ 2 :=
  (averaged_cavity_residual cavity q (cavityIterate z q n) bad t M₀
    hcard ht hq hgood hbad).trans hbudget

end LocalLaw
