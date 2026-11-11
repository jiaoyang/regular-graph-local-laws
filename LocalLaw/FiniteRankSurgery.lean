import LocalLaw.MatrixEntryStability

/-!
# Finite-rank surgery from old endpoint errors

The two resolvent update equations imply a comparison equation whose
reference factors use only the new model Green matrix. No lower bound on an
old defective diagonal, or norm bound on its reciprocal, is required.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance finiteRankSurgeryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Exact surgery comparison on the finite endpoint block. -/
theorem surgery_comparison_equation (R T P Q W : Matrix I I ℂ)
    (hT : T + R * W * T = R) (hQ : Q + Q * W * P = P) :
    (T - Q) + (1 - Q * W) * (R - P) * W * (T - Q) =
      (1 - Q * W) * (R - P) * (1 - W * Q) := by
  let A : Matrix I I ℂ := 1 - Q * W
  let E := R - P
  have hAP : A * P = Q := by
    dsimp only [A]
    rw [Matrix.sub_mul, Matrix.one_mul]
    exact ((eq_sub_iff_add_eq).mpr hQ).symm
  have hAR : A * R = Q + A * E := by
    calc
      _ = A * P + A * E := by dsimp only [E]; noncomm_ring
      _ = _ := by rw [hAP]
  have hmain : T + A * E * W * T = Q + A * E := by
    calc
      _ = A * T + Q * W * T + A * E * W * T := by dsimp only [A]; noncomm_ring
      _ = A * T + (Q + A * E) * W * T := by noncomm_ring
      _ = A * (T + R * W * T) := by rw [← hAR]; noncomm_ring
      _ = A * R := by rw [hT]
      _ = _ := hAR
  change (T - Q) + A * E * W * (T - Q) = A * E * (1 - W * Q)
  calc
    _ = (T + A * E * W * T) - Q - A * E * W * Q := by noncomm_ring
    _ = (Q + A * E) - Q - A * E * W * Q := by rw [hmain]
    _ = _ := by noncomm_ring

omit [DecidableEq I] in
/-- Product row sums are genuine finite convolution estimates. -/
theorem matrix_product_row_sum_bound (A B : Matrix I I ℂ) (r s : ℝ)
    (hs : 0 ≤ s) (hA : ∀ i, ∑ j, ‖A i j‖ ≤ r)
    (hB : ∀ i, ∑ j, ‖B i j‖ ≤ s) (i : I) :
    (∑ j, ‖(A * B) i j‖) ≤ r * s := by
  calc
    _ ≤ ∑ j, ∑ k, ‖A i k‖ * ‖B k j‖ :=
      Finset.sum_le_sum (fun j _ => matrix_mul_entry_norm_le A B i j)
    _ = ∑ k, ‖A i k‖ * (∑ j, ‖B k j‖) := by rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]
    _ ≤ ∑ k, ‖A i k‖ * s := Finset.sum_le_sum (fun k _ =>
      mul_le_mul_of_nonneg_left (hB k) (norm_nonneg _))
    _ = (∑ k, ‖A i k‖) * s := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hA i) hs

/-- Actual endpoint errors propagate through surgery with a dimension-free
constant, once dimension times the old error is small. The reference inputs
are only row/column sums of the new Green block and coupling sums. -/
theorem surgery_entry_stability (R T P Q W : Matrix I I ℂ)
    (hT : T + R * W * T = R) (hQ : Q + Q * W * P = P)
    (C w δ : ℝ) (hC : 0 ≤ C) (hw : 0 ≤ w) (hδ : 0 ≤ δ)
    (hQrow : ∀ i, ∑ j, ‖Q i j‖ ≤ C) (hQcol : ∀ j, ∑ i, ‖Q i j‖ ≤ C)
    (hWrow : ∀ i, ∑ j, ‖W i j‖ ≤ w) (hWcol : ∀ j, ∑ i, ‖W i j‖ ≤ w)
    (hE : ∀ i j, ‖(R - P) i j‖ ≤ δ)
    (hsmall : (Fintype.card I : ℝ) * (1 + C * w) * w * δ ≤ 1 / 2)
    (i j : I) : ‖(T - Q) i j‖ ≤ 2 * (1 + C * w) ^ 2 * δ := by
  let A : Matrix I I ℂ := 1 - Q * W
  let B : Matrix I I ℂ := 1 - W * Q
  let E := R - P
  let F := T - Q
  let M := 1 + C * w
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hA : ∀ k, ∑ l, ‖A k l‖ ≤ M := by
    intro k
    have hprod := matrix_product_row_sum_bound Q W C w hw hQrow hWrow k
    calc
      _ ≤ ∑ l, (‖(1 : Matrix I I ℂ) k l‖ + ‖(Q * W) k l‖) :=
        Finset.sum_le_sum (fun l _ => norm_sub_le _ _)
      _ = 1 + ∑ l, ‖(Q * W) k l‖ := by simp [Finset.sum_add_distrib, Matrix.one_apply, apply_ite norm]
      _ ≤ M := add_le_add_left hprod 1
  have hB : ∀ l, ∑ k, ‖B k l‖ ≤ M := by
    intro l
    have hprod := matrix_product_row_sum_bound Q.transpose W.transpose C w hw hQcol hWcol l
    have hid : Q.transpose * W.transpose = (W * Q).transpose := (Matrix.transpose_mul W Q).symm
    rw [hid] at hprod
    calc
      _ ≤ ∑ k, (‖(1 : Matrix I I ℂ) k l‖ + ‖(W * Q) k l‖) :=
        Finset.sum_le_sum (fun k _ => norm_sub_le _ _)
      _ = 1 + ∑ k, ‖(W * Q) k l‖ := by simp [Finset.sum_add_distrib, Matrix.one_apply, apply_ite norm]
      _ ≤ M := add_le_add_left hprod 1
  letI : Nonempty I := ⟨i⟩
  obtain ⟨p, hp⟩ := Finite.exists_max (fun ij : I × I => ‖F ij.1 ij.2‖)
  let Γ := ‖F p.1 p.2‖
  have hΓ : ∀ k l, ‖F k l‖ ≤ Γ := fun k l => hp (k, l)
  have hΓ0 : 0 ≤ Γ := norm_nonneg _
  have hWF : ∀ k l, ‖(W * F) k l‖ ≤ w * Γ := fun k l =>
    matrix_mul_entry_bound_of_row W F k l w Γ hΓ0 (hWrow k) (fun u => hΓ u l)
  have hEWF : ∀ k l, ‖(E * (W * F)) k l‖ ≤ (Fintype.card I : ℝ) * δ * (w * Γ) := by
    intro k l
    apply matrix_mul_entry_bound_of_row E (W * F) k l _ _ (by positivity) _ (fun u => hWF u l)
    calc
      _ ≤ ∑ _u : I, δ := Finset.sum_le_sum (fun u _ => hE k u)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hAEWF : ∀ k l, ‖(A * E * W * F) k l‖ ≤
      (Fintype.card I : ℝ) * M * w * δ * Γ := by
    intro k l
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
    have hh := matrix_mul_entry_bound_of_row A (E * (W * F)) k l M _ (by positivity)
      (hA k) (fun u => hEWF u l)
    exact hh.trans_eq (by ring)
  have hEB : ∀ k l, ‖(E * B) k l‖ ≤ δ * M := fun k l =>
    matrix_mul_entry_bound_of_column E B k l δ M hδ (fun u => hE k u) (hB l)
  have hAEB : ∀ k l, ‖(A * E * B) k l‖ ≤ M ^ 2 * δ := by
    intro k l
    rw [Matrix.mul_assoc]
    have hh := matrix_mul_entry_bound_of_row A (E * B) k l M _ (by positivity)
      (hA k) (fun u => hEB u l)
    exact hh.trans_eq (by ring)
  have hid := surgery_comparison_equation R T P Q W hT hQ
  have hentry : ∀ k l, ‖F k l‖ ≤ (Fintype.card I : ℝ) * M * w * δ * Γ + M ^ 2 * δ := by
    intro k l
    have hh := congrArg (fun X : Matrix I I ℂ => X k l) hid
    change F k l + (A * E * W * F) k l = (A * E * B) k l at hh
    have heq : F k l = (A * E * B) k l - (A * E * W * F) k l := (eq_sub_iff_add_eq).mpr hh
    rw [heq]
    exact ((norm_sub_le _ _).trans (add_le_add (hAEB k l) (hAEWF k l))).trans_eq (add_comm _ _)
  have hmax := hentry p.1 p.2
  change Γ ≤ (Fintype.card I : ℝ) * M * w * δ * Γ + M ^ 2 * δ at hmax
  have hscaled := mul_le_mul_of_nonneg_right hsmall hΓ0
  change (Fintype.card I : ℝ) * M * w * δ * Γ ≤ 1 / 2 * Γ at hscaled
  have hhalf : Γ ≤ 1 / 2 * Γ + M ^ 2 * δ := hmax.trans (add_le_add_right hscaled _)
  have absorb (x y : ℝ) (h : x ≤ (1 / 2 : ℝ) * x + y) : x ≤ 2 * y := by linarith
  have habsorb : Γ ≤ 2 * M ^ 2 * δ := (absorb Γ (M ^ 2 * δ) hhalf).trans_eq (by ring)
  exact (hΓ i j).trans habsorb

end LocalLaw
