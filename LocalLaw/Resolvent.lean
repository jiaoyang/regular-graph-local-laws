import LocalLaw.FiniteModel

/-!
# Positivity and well-definedness of boundary resolvents

A Hermitian matrix minus zI minus a nonnegative diagonal boundary self-energy
has no kernel when Im(z)>0 and Im(w)≥0. This proves invertibility of the finite
model used in the paper for actual upper-half-plane cavity parameters.
-/

open scoped BigOperators Matrix

namespace LocalLaw

section
variable {V : Type*} [Fintype V]

/-- The Hermitian quadratic form is real. -/
theorem hermitian_quadraticForm_im (H : Matrix V V ℂ) (hH : H.IsHermitian) (x : V → ℂ) :
    (star x ⬝ᵥ (H *ᵥ x)).im = 0 := by
  have hstar : star (star x ⬝ᵥ (H *ᵥ x)) = star x ⬝ᵥ (H *ᵥ x) := by
    calc
      star (star x ⬝ᵥ (H *ᵥ x)) = star (H *ᵥ x) ⬝ᵥ x := by
        simp only [dotProduct, star_sum, star_mul, Pi.star_apply, star_star]
      _ = (star x ᵥ* H.conjTranspose) ⬝ᵥ x := by rw [Matrix.star_mulVec]
      _ = star x ⬝ᵥ (H *ᵥ x) := by rw [← Matrix.dotProduct_mulVec, hH.eq]
  have him := congrArg Complex.im hstar
  change -(star x ⬝ᵥ (H *ᵥ x)).im = (star x ⬝ᵥ (H *ᵥ x)).im at him
  linarith

/-- The norm-square quadratic form of the identity. -/
theorem dotProduct_star_self (x : V → ℂ) :
    star x ⬝ᵥ x = (↑(∑ i, ‖x i‖ ^ 2) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, ← Complex.conj_mul', Complex.ofReal_sum,
    Complex.ofReal_pow, starRingEnd_apply]

variable [DecidableEq V]

/-- A real diagonal quadratic form is the corresponding weighted square sum. -/
theorem dotProduct_real_diagonal (d : V → ℝ) (x : V → ℂ) :
    star x ⬝ᵥ ((Matrix.diagonal (fun i => (d i : ℂ))) *ᵥ x) =
      (↑(∑ i, d i * ‖x i‖ ^ 2) : ℂ) := by
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Pi.mul_apply,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Complex.conj_mul']
  simp only [starRingEnd_apply]
  ring

/-- The actual finite boundary model is nonsingular in the Herglotz domain. -/
theorem boundaryMatrix_isUnit (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (d : V → ℝ) (hd : ∀ i, 0 ≤ d i) (w z : ℂ)
    (hz : 0 < z.im) (hw : 0 ≤ w.im) :
    IsUnit (boundaryMatrix H (Matrix.diagonal (fun i => (d i : ℂ))) w z) := by
  let A := boundaryMatrix H (Matrix.diagonal (fun i => (d i : ℂ))) w z
  have hker : ∀ x : V → ℂ, A *ᵥ x = 0 → x = 0 := by
    intro x hx
    have hquad : star x ⬝ᵥ (A *ᵥ x) =
        star x ⬝ᵥ (H *ᵥ x) - z * (↑(∑ i, ‖x i‖ ^ 2) : ℂ) -
          w * (↑(∑ i, d i * ‖x i‖ ^ 2) : ℂ) := by
      dsimp [A, boundaryMatrix, spectralMatrix]
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
        Matrix.one_mulVec, Matrix.smul_mulVec_assoc, dotProduct_sub, dotProduct_sub,
        dotProduct_smul, dotProduct_smul, dotProduct_star_self, dotProduct_real_diagonal]
      rfl
    rw [hx] at hquad
    have him := congrArg Complex.im hquad
    simp only [dotProduct_zero, Complex.zero_im, Complex.sub_im,
      hermitian_quadraticForm_im H hH, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add] at him
    have hnorm : 0 ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hweighted : 0 ≤ ∑ i, d i * ‖x i‖ ^ 2 :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hd i) (sq_nonneg _))
    have hprod : 0 ≤ w.im * ∑ i, d i * ‖x i‖ ^ 2 := mul_nonneg hw hweighted
    have hzero : (∑ i, ‖x i‖ ^ 2) = 0 := by nlinarith
    funext i
    apply norm_eq_zero.mp
    have hi : ‖x i‖ ^ 2 ≤ ∑ j, ‖x j‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖x j‖) (Finset.mem_univ i)
    rw [hzero] at hi
    nlinarith [norm_nonneg (x i)]
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  apply sub_eq_zero.mp
  apply hker
  rw [Matrix.mulVec_sub, hxy, sub_self]

/-- Positive imaginary parts of resolvent diagonals follow from Ward. -/
theorem green_diagonal_im_nonneg (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (i : V) : 0 ≤ (green H z i i).im := by
  have hw := ward_identity H hH z hz i
  have hs : 0 ≤ ∑ k, ‖green H z i k‖ ^ 2 :=
    Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hdiv : 0 ≤ (green H z i i).im / z.im := hw ▸ hs
  have hmul := (le_div_iff₀ hz).mp hdiv
  simpa using hmul

/-- A transpose identity gives column Ward estimates without assuming
that the Hermitian input is real symmetric. -/
theorem green_transpose (H : Matrix V V ℂ) (z : ℂ) :
    (green H z).transpose = green H.transpose z := by
  unfold green
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  simp only [spectralMatrix, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one]

theorem ward_identity_column (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (i : V) :
    ∑ k, ‖green H z k i‖ ^ 2 = (green H z i i).im / z.im := by
  have hw := ward_identity H.transpose hH.transpose z hz i
  rw [← green_transpose] at hw
  simpa only [Matrix.transpose_apply] using hw

/-- Universal diagonal resolvent bound, derived directly from Ward. -/
theorem green_diagonal_norm_le (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (i : V) : ‖green H z i i‖ ≤ 1 / z.im := by
  have hi : ‖green H z i i‖ ^ 2 ≤ ∑ k, ‖green H z i k‖ ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg ‖green H z i k‖) (Finset.mem_univ i)
  rw [ward_identity H hH z hz i] at hi
  have him : (green H z i i).im ≤ ‖green H z i i‖ :=
    (le_abs_self _).trans (Complex.abs_im_le_norm _)
  have hquad := (le_div_iff₀ hz).mp hi
  apply (le_div_iff₀ hz).2
  by_cases hn : ‖green H z i i‖ = 0
  · simp [hn]
  · have hnpos : 0 < ‖green H z i i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    by_contra hh
    have hlt : 1 < ‖green H z i i‖ * z.im := lt_of_not_ge hh
    have hprod := mul_pos hnpos (sub_pos.mpr hlt)
    nlinarith

/-- Every entry satisfies the usual 1/Im(z) estimate. -/
theorem green_entry_norm_le (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (i j : V) : ‖green H z i j‖ ≤ 1 / z.im := by
  have hi : ‖green H z i j‖ ^ 2 ≤ ∑ k, ‖green H z i k‖ ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg ‖green H z i k‖) (Finset.mem_univ j)
  rw [ward_identity H hH z hz i] at hi
  have him : (green H z i i).im ≤ 1 / z.im :=
    ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans
      (green_diagonal_norm_le H hH z hz i)
  have hsq : ‖green H z i j‖ ^ 2 ≤ (1 / z.im) ^ 2 := by
    calc
      _ ≤ (green H z i i).im / z.im := hi
      _ ≤ (1 / z.im) / z.im := div_le_div_of_nonneg_right him hz.le
      _ = (1 / z.im) ^ 2 := by ring
  nlinarith [norm_nonneg (green H z i j), div_pos (by norm_num : (0:ℝ)<1) hz]

/-- Pointwise entry continuity at two upper-half-plane parameters. The
constant is uniform once both imaginary parts are bounded below. -/
theorem green_entry_lipschitz (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z w : ℂ) (η₀ C : ℝ) (hη : 0 < η₀)
    (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im)
    (i j : V) (hdiagz : (green H z i i).im ≤ C)
    (hdiagw : (green H w j j).im ≤ C) :
    ‖green H z i j - green H w i j‖ ≤ (C / η₀) * dist z w := by
  have hzp : 0 < z.im := hη.trans_le hz
  have hwp : 0 < w.im := hη.trans_le hw
  have hC : 0 ≤ C := (green_diagonal_im_nonneg H hH z hzp i).trans hdiagz
  have hrow : (∑ k, ‖green H z i k‖ ^ 2) ≤ C / η₀ := by
    rw [ward_identity H hH z hzp i]
    exact div_le_div₀ hC hdiagz hη hz
  have hcol : (∑ k, ‖green H w k j‖ ^ 2) ≤ C / η₀ := by
    rw [ward_identity_column H hH w hwp j]
    exact div_le_div₀ hC hdiagw hη hw
  have hproduct : ‖(green H z * green H w) i j‖ ≤ C / η₀ := by
    calc
      _ ≤ ∑ k, ‖green H z i k * green H w k j‖ := by
        simpa only [Matrix.mul_apply] using
          (norm_sum_le Finset.univ (fun k => green H z i k * green H w k j))
      _ ≤ ∑ k, ((‖green H z i k‖ ^ 2 + ‖green H w k j‖ ^ 2) / 2) := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul]
        nlinarith [sq_nonneg (‖green H z i k‖ - ‖green H w k j‖)]
      _ = ((∑ k, ‖green H z i k‖ ^ 2) + (∑ k, ‖green H w k j‖ ^ 2)) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib]
      _ ≤ C / η₀ := by linarith
  have hid := congrFun (congrFun (green_sub_green H hH z w hzp hwp) i) j
  change green H z i j - green H w i j =
    (z - w) * (green H z * green H w) i j at hid
  rw [hid, norm_mul]
  exact (mul_le_mul_of_nonneg_left hproduct (norm_nonneg _)).trans_eq
    (by rw [dist_eq_norm]; ring)

/-- Coarse uniform continuity needs no spectral regularity event. -/
theorem green_entry_lipschitz_universal (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z w : ℂ) (η₀ : ℝ) (hη : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im)
    (i j : V) :
    ‖green H z i j - green H w i j‖ ≤ (1 / η₀ ^ 2) * dist z w := by
  have hzp : 0 < z.im := hη.trans_le hz
  have hwp : 0 < w.im := hη.trans_le hw
  have hdiagz : (green H z i i).im ≤ 1 / η₀ := by
    calc
      _ ≤ ‖green H z i i‖ := (le_abs_self _).trans (Complex.abs_im_le_norm _)
      _ ≤ 1 / z.im := green_diagonal_norm_le H hH z hzp i
      _ ≤ 1 / η₀ := one_div_le_one_div_of_le hη hz
  have hdiagw : (green H w j j).im ≤ 1 / η₀ := by
    calc
      _ ≤ ‖green H w j j‖ := (le_abs_self _).trans (Complex.abs_im_le_norm _)
      _ ≤ 1 / w.im := green_diagonal_norm_le H hH w hwp j
      _ ≤ 1 / η₀ := one_div_le_one_div_of_le hη hw
  simpa only [div_div, pow_two] using
    green_entry_lipschitz H hH z w η₀ (1 / η₀) hη hz hw i j hdiagz hdiagw

/-- The cavity average of the normalized adjacency matrix is in the closed
upper half-plane, since every minor resolvent has nonnegative diagonal
imaginary part. -/
theorem cavityAverage_im_nonneg (G : SimpleGraph V) (d : ℕ)
    (z : ℂ) (hz : 0 < z.im) : 0 ≤ (cavityAverage G d z).im := by
  classical
  have hcoef : ((Fintype.card V : ℂ) * (d : ℂ))⁻¹ =
      (↑(((Fintype.card V : ℝ) * (d : ℝ))⁻¹) : ℂ) := by
    push_cast
    rfl
  unfold cavityAverage
  rw [hcoef]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  apply mul_nonneg
  · positivity
  · rw [Complex.im_sum]
    apply Finset.sum_nonneg
    intro j _
    rw [Complex.im_sum]
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact green_diagonal_im_nonneg _
        (deletedMatrix_isHermitian _ (normalizedAdjacency_isHermitian G d) j) z hz i
    · simp

end

end LocalLaw
