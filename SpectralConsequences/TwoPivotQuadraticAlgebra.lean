import SpectralConsequences.InverseSecondOrder

/-! # The quadratic two-pivot covariance expansion

The two large within-edge entries are normalized by a common deterministic
q-dependent tree diagonal. All cross-edge entries are small. The genuine
inverse expansion then has a quadratic, rather than linear, error.
-/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw

/-- The scalar Schur correction through two retained vertices. -/
def twoPivotSchur (U : Matrix (Fin 2) (Fin 2) ℂ) (l r : Fin 2 → ℂ) : ℂ :=
  ∑ i, ∑ j, l i * U⁻¹ i j * r j

/-- A two-pivot inverse remainder gives the desired quadratic covariance
expansion. The deterministic factor a may be alpha*q; q need not solve the
semicircle equation. -/
theorem twoPivot_quadratic_expansion (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : IsUnit U) (l r : Fin 2 → ℂ) (t a : ℂ) (ht : t ≠ 0)
    (C P δ : ℝ) (hC : 1 ≤ C) (hP : 1 ≤ P) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (htnorm : ‖t‖ ≤ C) (htinv : ‖t⁻¹‖ ≤ P) (hanorm : ‖a‖ ≤ 1)
    (hl : ∀ i, ‖l i‖ ≤ C) (hr : ∀ i, ‖r i‖ ≤ C)
    (hl0 : ‖l 0+a*t‖ ≤ δ) (hr1 : ‖r 1+a*t‖ ≤ δ)
    (hl1 : ‖l 1‖ ≤ δ) (hr0 : ‖r 0‖ ≤ δ)
    (hdiag : ∀ i, ‖U i i-t‖ ≤ δ)
    (hoff : ∀ i j, i ≠ j → ‖U i j‖ ≤ δ)
    (hsmall : 2*P*δ ≤ 1/2) :
    ‖twoPivotSchur U l r + a*r 0 + a*l 1 + a^2*U 0 1‖ ≤
      (2*P+(4*C+1)*P^2+16*C^2*P^3)*δ^2 := by
  let D : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (fun _ => t)
  have hD : IsUnit D := by
    apply (Matrix.isUnit_iff_isUnit_det D).mpr
    simp only [D,Matrix.det_fin_two,Matrix.diagonal_apply_eq,
      Matrix.diagonal_apply_ne _ (by decide : (0:Fin 2) ≠ 1),
      Matrix.diagonal_apply_ne _ (by decide : (1:Fin 2) ≠ 0),mul_zero,sub_zero]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero ht ht)
  have hDinv : D⁻¹ = Matrix.diagonal (fun _ : Fin 2 => t⁻¹) := by
    apply Matrix.inv_eq_left_inv
    simp [D,Matrix.diagonal_mul_diagonal,ht]
  have hDrow (i : Fin 2) : ∑ j, ‖D⁻¹ i j‖ ≤ P := by
    rw [hDinv]
    fin_cases i <;> simpa [Matrix.diagonal_apply,Fin.sum_univ_two] using htinv
  have hDcol (j : Fin 2) : ∑ i, ‖D⁻¹ i j‖ ≤ P := by
    rw [hDinv]
    fin_cases j <;> simpa [Matrix.diagonal_apply,Fin.sum_univ_two] using htinv
  have hentry (i j : Fin 2) : ‖(U-D) i j‖ ≤ δ := by
    by_cases hij : i=j
    · subst j
      simpa only [Matrix.sub_apply,D,Matrix.diagonal_apply_eq] using hdiag i
    · simpa only [Matrix.sub_apply,D,Matrix.diagonal_apply_ne _ hij,sub_zero] using hoff i j hij
  let V := (U⁻¹-D⁻¹)+D⁻¹*(U-D)*D⁻¹
  have hV (i j : Fin 2) : ‖V i j‖ ≤ 4*P^3*δ^2 := by
    have h := inverse_first_order_remainder U D hU hD P δ (by linarith) hδ
      hDrow hDcol hentry (by simpa only [Fintype.card_fin,Nat.cast_ofNat] using hsmall) i j
    simpa only [V,Fintype.card_fin,Nat.cast_ofNat,show (2:ℝ)*2=4 by norm_num] using h
  have hVentry (i j : Fin 2) : V i j = U⁻¹ i j -
      (if i=j then t⁻¹ else 0)+t⁻¹^2*(U i j-(if i=j then t else 0)) := by
    rw [show V = (U⁻¹-D⁻¹)+D⁻¹*(U-D)*D⁻¹ by rfl,hDinv]
    fin_cases i <;> fin_cases j <;>
      simp [D,Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal_apply] <;> ring
  let A := (l 0+a*t)*t⁻¹*r 0 + l 1*t⁻¹*(r 1+a*t)
  let B := -(t⁻¹^2)*(
    l 0*(U 0 0-t)*r 0 + l 1*(U 1 1-t)*r 1 + l 1*U 1 0*r 0 +
      (l 0*r 1-a^2*t^2)*U 0 1)
  let Z := ∑ i, ∑ j, l i*V i j*r j
  have hexact : twoPivotSchur U l r+a*r 0+a*l 1+a^2*U 0 1 = A+B+Z := by
    simp only [twoPivotSchur,A,B,Z,Fin.sum_univ_two,hVentry]
    norm_num only [Fin.isValue,Fin.reduceEq,if_true,if_false]
    field_simp [ht]
    ring_nf
    simp only [mul_assoc,←mul_pow,mul_inv_cancel₀ ht,one_pow,mul_one]
  have hAbound : ‖A‖ ≤ 2*P*δ^2 := by
    have h0 : ‖(l 0+a*t)*t⁻¹*r 0‖ ≤ δ*P*δ := by
      simpa only [norm_mul] using mul_le_mul
        (mul_le_mul hl0 htinv (norm_nonneg _) hδ) hr0 (norm_nonneg _) (by positivity)
    have h1 : ‖l 1*t⁻¹*(r 1+a*t)‖ ≤ δ*P*δ := by
      simpa only [norm_mul] using mul_le_mul
        (mul_le_mul hl1 htinv (norm_nonneg _) hδ) hr1 (norm_nonneg _) (by positivity)
    have hh := (norm_add_le _ _).trans (add_le_add h0 h1)
    dsimp only [A]
    nlinarith only [hh]
  have hprod : ‖l 0*r 1-a^2*t^2‖ ≤ 2*C*δ := by
    have hid : l 0*r 1-a^2*t^2 = (l 0+a*t)*r 1-a*t*(r 1+a*t) := by ring
    rw [hid]
    calc
      _ ≤ ‖l 0+a*t‖*‖r 1‖+‖a‖*‖t‖*‖r 1+a*t‖ := by
        simpa only [norm_mul] using norm_sub_le ((l 0+a*t)*r 1) (a*t*(r 1+a*t))
      _ ≤ δ*C+1*C*δ := add_le_add
        (mul_le_mul hl0 (hr 1) (norm_nonneg _) hδ)
        (mul_le_mul (mul_le_mul hanorm htnorm (norm_nonneg _) (by norm_num)) hr1
          (norm_nonneg _) (by positivity))
      _ = _ := by ring
  have hBbound : ‖B‖ ≤ (4*C+1)*P^2*δ^2 := by
    have hb0 : ‖l 0*(U 0 0-t)*r 0‖ ≤ C*δ^2 := by
      rw [norm_mul,norm_mul]
      have hh := mul_le_mul (mul_le_mul (hl 0) (hdiag 0) (norm_nonneg _) (by linarith))
        hr0 (norm_nonneg _) (by positivity)
      nlinarith only [hh]
    have hb1 : ‖l 1*(U 1 1-t)*r 1‖ ≤ C*δ^2 := by
      rw [norm_mul,norm_mul]
      have hh := mul_le_mul (mul_le_mul hl1 (hdiag 1) (norm_nonneg _) hδ)
        (hr 1) (norm_nonneg _) (by positivity)
      nlinarith only [hh]
    have hb2 : ‖l 1*U 1 0*r 0‖ ≤ δ^2 := by
      rw [norm_mul,norm_mul]
      have hh := mul_le_mul (mul_le_mul hl1 (hoff 1 0 (by decide)) (norm_nonneg _) hδ)
        hr0 (norm_nonneg _) (by positivity)
      nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδone)]
    have hb3 : ‖(l 0*r 1-a^2*t^2)*U 0 1‖ ≤ 2*C*δ^2 := by
      rw [norm_mul]
      have hh := mul_le_mul hprod (hoff 0 1 (by decide)) (norm_nonneg _) (by positivity)
      nlinarith only [hh]
    have hsum : ‖l 0*(U 0 0-t)*r 0+l 1*(U 1 1-t)*r 1+l 1*U 1 0*r 0+
        (l 0*r 1-a^2*t^2)*U 0 1‖ ≤ (4*C+1)*δ^2 := by
      have hh := (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hb0 hb1)) hb2)) hb3)
      nlinarith only [hh]
    dsimp only [B]
    rw [norm_mul,norm_neg,norm_pow]
    have hh := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) htinv 2) hsum (norm_nonneg _) (by positivity)
    nlinarith only [hh]
  have hZbound : ‖Z‖ ≤ 16*C^2*P^3*δ^2 := by
    calc
      _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖l i*V i j*r j‖ := by
        apply (norm_sum_le _ _).trans
        exact Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
      _ ≤ ∑ _i : Fin 2, ∑ _j : Fin 2, C*(4*P^3*δ^2)*C := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul,norm_mul]
        exact mul_le_mul (mul_le_mul (hl i) (hV i j) (norm_nonneg _) (by linarith))
          (hr j) (norm_nonneg _) (by positivity)
      _ = _ := by simp [Fin.sum_univ_two];ring
  rw [hexact]
  have hh := (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hAbound hBbound)) hZbound)
  nlinarith only [hh]

end SpectralConsequences
