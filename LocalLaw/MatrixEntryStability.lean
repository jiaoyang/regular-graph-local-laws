import Mathlib

/-!
# Entrywise inverse perturbation stability (the analytic core of Claim 5.7)

No entrywise maximum inequality is assumed. It is derived from the genuine
inverse identity and finite row/column product estimates, then absorbed under
an explicit dimension-times-error smallness condition.
-/

open scoped BigOperators

namespace LocalLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- A single entry of a product is bounded by the corresponding norm product
sum. -/
theorem matrix_mul_entry_norm_le (A B : Matrix V V ℂ) (i j : V) :
    ‖(A * B) i j‖ ≤ ∑ k, ‖A i k‖ * ‖B k j‖ := by
  simpa only [Matrix.mul_apply, norm_mul] using
    norm_sum_le Finset.univ (fun k => A i k * B k j)

omit [DecidableEq V] in
/-- A row-sum bound times a uniform bound on the required column. -/
theorem matrix_mul_entry_bound_of_row (A B : Matrix V V ℂ) (i j : V) (r c : ℝ)
    (hc : 0 ≤ c) (hrow : (∑ k, ‖A i k‖) ≤ r)
    (hB : ∀ k, ‖B k j‖ ≤ c) : ‖(A * B) i j‖ ≤ r * c := by
  calc
    ‖(A * B) i j‖ ≤ ∑ k, ‖A i k‖ * ‖B k j‖ := matrix_mul_entry_norm_le A B i j
    _ ≤ ∑ k, ‖A i k‖ * c := Finset.sum_le_sum (fun k _ =>
      mul_le_mul_of_nonneg_left (hB k) (norm_nonneg _))
    _ = (∑ k, ‖A i k‖) * c := (Finset.sum_mul ..).symm
    _ ≤ r * c := mul_le_mul_of_nonneg_right hrow hc

omit [DecidableEq V] in
/-- A uniform bound on the required row times a column-sum bound. -/
theorem matrix_mul_entry_bound_of_column (A B : Matrix V V ℂ) (i j : V) (c r : ℝ)
    (hc : 0 ≤ c) (hA : ∀ k, ‖A i k‖ ≤ c)
    (hcolumn : (∑ k, ‖B k j‖) ≤ r) : ‖(A * B) i j‖ ≤ c * r := by
  calc
    ‖(A * B) i j‖ ≤ ∑ k, ‖A i k‖ * ‖B k j‖ := matrix_mul_entry_norm_le A B i j
    _ ≤ ∑ k, c * ‖B k j‖ := Finset.sum_le_sum (fun k _ =>
      mul_le_mul_of_nonneg_right (hA k) (norm_nonneg _))
    _ = c * ∑ k, ‖B k j‖ := (Finset.mul_sum ..).symm
    _ ≤ c * r := mul_le_mul_of_nonneg_left hcolumn hc

/-- The exact identity (5.17), derived from nonsingular finite matrices. -/
theorem inverse_perturbation_identity (P W : Matrix V V ℂ)
    (hP : IsUnit P) (hPW : IsUnit (P + W)) :
    ((P + W)⁻¹ - P⁻¹) + P⁻¹ * W * ((P + W)⁻¹ - P⁻¹) + P⁻¹ * W * P⁻¹ = 0 := by
  let R := P⁻¹
  let S := (P + W)⁻¹
  have hRP : R * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP)
  have hprod : R * (P + W) * S = R := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv (P + W)
      ((Matrix.isUnit_iff_isUnit_det (P + W)).mp hPW), Matrix.mul_one]
  have hexp : S + R * W * S = R := by
    calc
      S + R * W * S = (R * P) * S + R * W * S := by rw [hRP, Matrix.one_mul]
      _ = R * (P + W) * S := by noncomm_ring
      _ = R := hprod
  change (S - R) + R * W * (S - R) + R * W * R = 0
  calc
    (S - R) + R * W * (S - R) + R * W * R = S + R * W * S - R := by noncomm_ring
    _ = 0 := by rw [hexp, sub_self]

/-- A finite-dimensional entrywise stability theorem. The row AND column
bounds on the reference inverse are essential. The proof uses an attained
maximum of entry norms; it does not substitute an operator norm. -/
theorem inverse_entry_stability (P W : Matrix V V ℂ)
    (hP : IsUnit P) (hPW : IsUnit (P + W)) (C δ : ℝ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hrow : ∀ i, (∑ k, ‖P⁻¹ i k‖) ≤ C)
    (hcolumn : ∀ j, (∑ k, ‖P⁻¹ k j‖) ≤ C)
    (hW : ∀ i j, ‖W i j‖ ≤ δ)
    (hsmall : (Fintype.card V : ℝ) * C * δ ≤ 1 / 2)
    (i j : V) : ‖((P + W)⁻¹ - P⁻¹) i j‖ ≤ 2 * C ^ 2 * δ := by
  classical
  letI : Nonempty V := ⟨i⟩
  let R := P⁻¹
  let X := (P + W)⁻¹ - P⁻¹
  obtain ⟨p, hp⟩ := Finite.exists_max (fun ij : V × V => ‖X ij.1 ij.2‖)
  let Γ := ‖X p.1 p.2‖
  have hΓ : ∀ k l, ‖X k l‖ ≤ Γ := fun k l => hp (k, l)
  have hΓnonneg : 0 ≤ Γ := norm_nonneg _
  have hWrow : ∀ k, (∑ l, ‖W k l‖) ≤ (Fintype.card V : ℝ) * δ := by
    intro k
    calc
      (∑ l, ‖W k l‖) ≤ ∑ _l : V, δ := Finset.sum_le_sum (fun l _ => hW k l)
      _ = (Fintype.card V : ℝ) * δ := by simp [nsmul_eq_mul]
  have hWX : ∀ k l, ‖(W * X) k l‖ ≤ (Fintype.card V : ℝ) * δ * Γ := by
    intro k l
    exact matrix_mul_entry_bound_of_row W X k l _ Γ hΓnonneg (hWrow k) (fun m => hΓ m l)
  have hRWX : ∀ k l, ‖(R * W * X) k l‖ ≤ (Fintype.card V : ℝ) * C * δ * Γ := by
    intro k l
    rw [Matrix.mul_assoc]
    have hb := matrix_mul_entry_bound_of_row R (W * X) k l C
      ((Fintype.card V : ℝ) * δ * Γ) (by positivity) (hrow k) (fun m => hWX m l)
    convert hb using 1
    ring
  have hWR : ∀ k l, ‖(W * R) k l‖ ≤ δ * C := by
    intro k l
    exact matrix_mul_entry_bound_of_column W R k l δ C hδ
      (fun m => hW k m) (hcolumn l)
  have hRWR : ∀ k l, ‖(R * W * R) k l‖ ≤ C ^ 2 * δ := by
    intro k l
    rw [Matrix.mul_assoc]
    have hb := matrix_mul_entry_bound_of_row R (W * R) k l C (δ * C)
      (mul_nonneg hδ hC) (hrow k) (fun m => hWR m l)
    convert hb using 1
    ring
  have hidentity : X + R * W * X + R * W * R = 0 := inverse_perturbation_identity P W hP hPW
  have hentry : ∀ k l, ‖X k l‖ ≤ (Fintype.card V : ℝ) * C * δ * Γ + C ^ 2 * δ := by
    intro k l
    have hid := congrArg (fun M : Matrix V V ℂ => M k l) hidentity
    change X k l + (R * W * X) k l + (R * W * R) k l = 0 at hid
    have hx : X k l = -((R * W * X) k l + (R * W * R) k l) := by linear_combination hid
    rw [hx, norm_neg]
    exact (norm_add_le _ _).trans (add_le_add (hRWX k l) (hRWR k l))
  have hmax := hentry p.1 p.2
  change Γ ≤ (Fintype.card V : ℝ) * C * δ * Γ + C ^ 2 * δ at hmax
  have hsmallΓ := mul_le_mul_of_nonneg_right hsmall hΓnonneg
  have habsorb : Γ ≤ 2 * C ^ 2 * δ := by nlinarith
  exact (hΓ i j).trans habsorb

end LocalLaw
