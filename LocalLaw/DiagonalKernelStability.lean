import LocalLaw.LocalizationIdentity
import LocalLaw.ComplexDiagonalResolvent

/-!
# Weighted kernel stability for a nonuniform complex diagonal perturbation

The entrywise error and perturbed kernel bound are derived from genuine
inverses and a finite maximum. The diagonal entries may have different phases.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem complex_diagonal_kernel_product_bound (A B : Matrix V V ℂ) (e : V → ℂ)
    (d : V → ℝ) (τ : ℝ) (he : ∀ v, ‖e v‖ ≤ τ * d v)
    (K L : V → V → ℝ) (a b : ℝ) (hd : ∀ k, 0 ≤ d k)
    (hK : ∀ i j, 0 ≤ K i j) (ha : 0 ≤ a) (hb : 0 ≤ b) (hτ : 0 ≤ τ)
    (hA : ∀ i j, ‖A i j‖ ≤ a * K i j) (hB : ∀ i j, ‖B i j‖ ≤ b * L i j)
    (i j : V) (R : ℝ) (hconv : (∑ k, d k * K i k * L k j) ≤ R) :
    ‖(A * Matrix.diagonal e * B) i j‖ ≤ a * b * τ * R := by
  calc
    _ ≤ ∑ k, ‖A i k‖ * ‖e k‖ * ‖B k j‖ := by
      change ‖∑ k, (A * Matrix.diagonal e) i k * B k j‖ ≤ _
      simp only [Matrix.mul_diagonal]
      simpa only [norm_mul] using
        norm_sum_le Finset.univ (fun k => (A i k * e k) * B k j)
    _ ≤ ∑ k, (a * b * τ) * (d k * K i k * L k j) := by
      apply Finset.sum_le_sum
      intro k _
      have hleft := mul_le_mul (hA i k) (he k) (norm_nonneg _) (mul_nonneg ha (hK i k))
      have hprod := mul_le_mul hleft (hB k j) (norm_nonneg _)
        (mul_nonneg (mul_nonneg ha (hK i k)) (mul_nonneg hτ (hd k)))
      convert hprod using 1; ring
    _ = (a * b * τ) * ∑ k, d k * K i k * L k j := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hconv (mul_nonneg (mul_nonneg ha hb) hτ)

theorem complex_diagonal_kernel_stability (A : Matrix V V ℂ) (e : V → ℂ)
    (hA : IsUnit A) (hAe : IsUnit (A - Matrix.diagonal e))
    (d : V → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (he : ∀ v, ‖e v‖ ≤ τ * d v)
    (K B : V → V → ℝ) (C C₀ Ddiam : ℝ)
    (hd : ∀ k, 0 ≤ d k) (hK : ∀ i j, 0 ≤ K i j) (hB : ∀ i j, 0 < B i j)
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hDdiam : 0 ≤ Ddiam)
    (reference : ∀ i j, ‖A⁻¹ i j‖ ≤ C * K i j)
    (companion : ∀ i j, B i j ≤ Ddiam * K i j)
    (convolution : ∀ i j, (∑ k, d k * K i k * K k j) ≤ C₀ * B i j)
    (small : τ * C * C₀ * Ddiam ≤ 1 / 2) (i j : V) :
    ‖((A - Matrix.diagonal e)⁻¹ - A⁻¹) i j‖ ≤ 2 * τ * C ^ 2 * C₀ * B i j ∧
      ‖(A - Matrix.diagonal e)⁻¹ i j‖ ≤ 2 * C * K i j := by
  classical
  letI : Nonempty V := ⟨i⟩
  let E := Matrix.diagonal e
  let P₀ := A⁻¹
  let Pq := (A - E)⁻¹
  let X := Pq - P₀
  obtain ⟨p, hp⟩ := Finite.exists_max (fun ij : V × V => ‖X ij.1 ij.2‖ / B ij.1 ij.2)
  let Γ := ‖X p.1 p.2‖ / B p.1 p.2
  have hΓ : ∀ k l, ‖X k l‖ ≤ Γ * B k l := by
    intro k l
    exact (div_le_iff₀ (hB k l)).mp (hp (k, l))
  have hΓnonneg : 0 ≤ Γ := div_nonneg (norm_nonneg _) (hB p.1 p.2).le
  have hmaxeq : Γ * B p.1 p.2 = ‖X p.1 p.2‖ := div_mul_cancel₀ _ (ne_of_gt (hB p.1 p.2))
  have hconvB : ∀ k l, (∑ x, d x * K k x * B x l) ≤ Ddiam * C₀ * B k l := by
    intro k l
    calc
      _ ≤ ∑ x, Ddiam * (d x * K k x * K x l) := by
        apply Finset.sum_le_sum
        intro x _
        have h := mul_le_mul_of_nonneg_left (companion x l) (mul_nonneg (hd x) (hK k x))
        nlinarith
      _ = Ddiam * ∑ x, d x * K k x * K x l := (Finset.mul_sum ..).symm
      _ ≤ Ddiam * (C₀ * B k l) := mul_le_mul_of_nonneg_left (convolution k l) hDdiam
      _ = _ := by ring
  have hforce : ∀ k l, ‖(P₀ * E * P₀) k l‖ ≤ τ * C ^ 2 * C₀ * B k l := by
    intro k l
    have h := complex_diagonal_kernel_product_bound P₀ P₀ e d τ he K K C C hd hK hC hC hτ
      reference reference k l (C₀ * B k l) (convolution k l)
    convert h using 1; ring
  have hfeedback : ∀ k l, ‖(P₀ * E * X) k l‖ ≤ τ * C * C₀ * Ddiam * Γ * B k l := by
    intro k l
    have h := complex_diagonal_kernel_product_bound P₀ X e d τ he K B C Γ hd hK hC hΓnonneg hτ
      reference hΓ k l (Ddiam * C₀ * B k l) (hconvB k l)
    convert h using 1; ring
  have hplus : P₀ + X = Pq := by dsimp only [X]; abel
  have hidentity : X = P₀ * E * (P₀ + X) := by
    rw [hplus]
    have hid := matrix_inverse_difference A (A - E) hA hAe
    calc
      X = -(P₀ - Pq) := by dsimp only [X]; abel
      _ = -(A⁻¹ * ((A - E) - A) * (A - E)⁻¹) := by rw [hid]
      _ = _ := by dsimp only [P₀, Pq]; noncomm_ring
  have hentry : ∀ k l, ‖X k l‖ ≤
      τ * C ^ 2 * C₀ * B k l + τ * C * C₀ * Ddiam * Γ * B k l := by
    intro k l
    have hid := congrArg (fun M : Matrix V V ℂ => M k l) hidentity
    rw [Matrix.mul_add] at hid
    change X k l = (P₀ * E * P₀) k l + (P₀ * E * X) k l at hid
    rw [hid]
    exact (norm_add_le _ _).trans (add_le_add (hforce k l) (hfeedback k l))
  have hscalar : Γ ≤ τ * C ^ 2 * C₀ + τ * C * C₀ * Ddiam * Γ := by
    apply (mul_le_mul_right (hB p.1 p.2)).mp
    calc
      _ = ‖X p.1 p.2‖ := hmaxeq
      _ ≤ _ := hentry p.1 p.2
      _ = _ := by ring
  have hsmallΓ := mul_le_mul_of_nonneg_right small hΓnonneg
  have habsorb : Γ ≤ 2 * τ * C ^ 2 * C₀ := by nlinarith
  have hdiff : ‖X i j‖ ≤ 2 * τ * C ^ 2 * C₀ * B i j :=
    (hΓ i j).trans (mul_le_mul_of_nonneg_right habsorb (hB i j).le)
  refine ⟨hdiff, ?_⟩
  have hconstant : 2 * τ * C ^ 2 * C₀ * Ddiam ≤ C := by
    have h := mul_le_mul_of_nonneg_left small (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC)
    nlinarith
  have hcap : ‖X i j‖ ≤ C * K i j := by
    apply hdiff.trans
    apply (mul_le_mul_of_nonneg_left (companion i j) (by positivity)).trans
    nlinarith [mul_le_mul_of_nonneg_right hconstant (hK i j)]
  change ‖Pq i j‖ ≤ _
  rw [← hplus]
  exact (norm_add_le (P₀ i j) (X i j)).trans (by nlinarith [reference i j])

end LocalLaw
