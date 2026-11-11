import LocalLaw.Resolvent

/-!
# Ward bounds and two-variable continuity for dissipative boundary models

For H Hermitian and a nonnegative real diagonal D, the inverse of
H-zI-uD is a genuine inverse when Im z>0 and Im u>=0. Weighted Ward identities
are proved by evaluating its solved columns against the quadratic form.
-/

open scoped BigOperators Matrix

namespace LocalLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact weighted column Ward identity for the dissipative boundary model. -/
theorem boundary_ward_column_exact (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (d : V → ℝ) (hd : ∀ k, 0 ≤ d k) (u z : ℂ)
    (hz : 0 < z.im) (hu : 0 ≤ u.im) (i : V) :
    (boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z i i).im =
      z.im * ∑ k, ‖boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z k i‖ ^ 2 +
      u.im * ∑ k, d k * ‖boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z k i‖ ^ 2 := by
  let D : Matrix V V ℂ := Matrix.diagonal (fun k => (d k : ℂ))
  let A := boundaryMatrix H D u z
  let P := boundaryGreen H D u z
  let x : V → ℂ := fun k => P k i
  have hunit : IsUnit A := boundaryMatrix_isUnit H hH d hd u z hz hu
  have hprod : A * P = 1 :=
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hunit)
  have hsolve : A *ᵥ x = Pi.single i 1 := by
    funext k
    have hk := congrArg (fun M : Matrix V V ℂ => M k i) hprod
    simpa only [Matrix.mul_apply, Matrix.one_apply, Matrix.mulVec, dotProduct,
      x, Pi.single_apply, eq_comm] using hk
  have hq : star x ⬝ᵥ (A *ᵥ x) = star (P i i) := by
    rw [hsolve, dotProduct_single, mul_one]
    rfl
  have hquad : star x ⬝ᵥ (A *ᵥ x) =
      star x ⬝ᵥ (H *ᵥ x) - z * (↑(∑ k, ‖x k‖ ^ 2) : ℂ) -
        u * (↑(∑ k, d k * ‖x k‖ ^ 2) : ℂ) := by
    dsimp [A, D, boundaryMatrix, spectralMatrix]
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
      Matrix.one_mulVec, Matrix.smul_mulVec_assoc, dotProduct_sub, dotProduct_sub,
      dotProduct_smul, dotProduct_smul, dotProduct_star_self, dotProduct_real_diagonal]
    rfl
  have him := congrArg Complex.im (hq.symm.trans hquad)
  simp only [Complex.star_def, Complex.conj_im, Complex.sub_im,
    hermitian_quadraticForm_im H hH, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_add] at him
  change (P i i).im = z.im * ∑ k, ‖x k‖ ^ 2 + u.im * ∑ k, d k * ‖x k‖ ^ 2
  linarith

/-- Transposition exchanges rows and columns without requiring H real. -/
theorem boundaryGreen_transpose_diagonal (H : Matrix V V ℂ) (d : V → ℝ) (u z : ℂ) :
    (boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z).transpose =
      boundaryGreen H.transpose (Matrix.diagonal (fun k => (d k : ℂ))) u z := by
  unfold boundaryGreen
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  simp only [boundaryMatrix, spectralMatrix, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.diagonal_transpose]

/-- Exact weighted row Ward identity. -/
theorem boundary_ward_row_exact (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (d : V → ℝ) (hd : ∀ k, 0 ≤ d k) (u z : ℂ)
    (hz : 0 < z.im) (hu : 0 ≤ u.im) (i : V) :
    (boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z i i).im =
      z.im * ∑ k, ‖boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z i k‖ ^ 2 +
      u.im * ∑ k, d k * ‖boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z i k‖ ^ 2 := by
  have h := boundary_ward_column_exact H.transpose hH.transpose d hd u z hz hu i
  rw [← boundaryGreen_transpose_diagonal] at h
  simpa only [Matrix.transpose_apply] using h

theorem boundary_ward_column (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (d : V → ℝ) (hd : ∀ k, 0 ≤ d k) (u z : ℂ)
    (hz : 0 < z.im) (hu : 0 ≤ u.im) (i : V) :
    z.im * ∑ k, ‖boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z k i‖ ^ 2 ≤
      (boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z i i).im := by
  rw [boundary_ward_column_exact H hH d hd u z hz hu i]
  have hsum : 0 ≤ ∑ k, d k *
      ‖boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z k i‖ ^ 2 :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hd k) (sq_nonneg _))
  linarith [mul_nonneg hu hsum]

theorem boundary_ward_row (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (d : V → ℝ) (hd : ∀ k, 0 ≤ d k) (u z : ℂ)
    (hz : 0 < z.im) (hu : 0 ≤ u.im) (i : V) :
    z.im * ∑ k, ‖boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z i k‖ ^ 2 ≤
      (boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z i i).im := by
  have h := boundary_ward_column H.transpose hH.transpose d hd u z hz hu i
  rw [← boundaryGreen_transpose_diagonal] at h
  simpa only [Matrix.transpose_apply] using h

/-- A dissipative boundary Green function has nonnegative diagonal imaginary
parts, before any local graph law is available. -/
theorem boundaryGreen_diagonal_im_nonneg (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (d : V → ℝ) (hd : ∀ k, 0 ≤ d k) (u z : ℂ)
    (hz : 0 < z.im) (hu : 0 ≤ u.im) (i : V) :
    0 ≤ (boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z i i).im := by
  have hs : 0 ≤ z.im * ∑ k,
      ‖boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z i k‖ ^ 2 := by
    positivity
  exact hs.trans (boundary_ward_row H hH d hd u z hz hu i)


/-- Universal diagonal norm bound for a dissipative boundary model. -/
theorem boundaryGreen_diagonal_norm_le (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (d : V → ℝ) (hd : ∀ k, 0 ≤ d k) (u z : ℂ)
    (hz : 0 < z.im) (hu : 0 ≤ u.im) (i : V) :
    ‖boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z i i‖ ≤ 1 / z.im := by
  let P := boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z
  have hterm : ‖P i i‖ ^ 2 ≤ ∑ k, ‖P i k‖ ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg ‖P i k‖) (Finset.mem_univ i)
  have hward := boundary_ward_row H hH d hd u z hz hu i
  have hquad : z.im * ‖P i i‖ ^ 2 ≤ (P i i).im :=
    (mul_le_mul_of_nonneg_left hterm hz.le).trans hward
  have him : (P i i).im ≤ ‖P i i‖ :=
    (le_abs_self _).trans (Complex.abs_im_le_norm _)
  change ‖P i i‖ ≤ 1 / z.im
  apply (le_div_iff₀ hz).2
  by_cases hn : ‖P i i‖ = 0
  · simp [hn]
  · have hnpos : 0 < ‖P i i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    by_contra hh
    have hlt : 1 < ‖P i i‖ * z.im := lt_of_not_ge hh
    have hprod := mul_pos hnpos (sub_pos.mpr hlt)
    nlinarith

/-- Row and column square sums are bounded uniformly above the line eta0. -/
theorem boundary_square_sum_bounds (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (d : V → ℝ) (hd : ∀ k, 0 ≤ d k) (u z : ℂ) (η₀ : ℝ)
    (hη₀ : 0 < η₀) (hz : η₀ ≤ z.im) (hu : 0 ≤ u.im) (i : V) :
    (∑ k, ‖boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z i k‖ ^ 2)
        ≤ 1 / η₀ ^ 2 ∧
    (∑ k, ‖boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z k i‖ ^ 2)
        ≤ 1 / η₀ ^ 2 := by
  have hzp : 0 < z.im := hη₀.trans_le hz
  let P := boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z
  have him : (P i i).im ≤ 1 / η₀ := by
    calc
      _ ≤ ‖P i i‖ := (le_abs_self _).trans (Complex.abs_im_le_norm _)
      _ ≤ 1 / z.im := boundaryGreen_diagonal_norm_le H hH d hd u z hzp hu i
      _ ≤ 1 / η₀ := one_div_le_one_div_of_le hη₀ hz
  have aux : ∀ S : ℝ, 0 ≤ S → z.im * S ≤ (P i i).im → S ≤ 1 / η₀ ^ 2 := by
    intro S hS hward
    have hscaled : η₀ * S ≤ 1 / η₀ :=
      ((mul_le_mul_of_nonneg_right hz hS).trans hward).trans him
    have hdiv : S ≤ (1 / η₀) / η₀ := (le_div_iff₀ hη₀).2 (by nlinarith)
    simpa only [div_div, pow_two] using hdiv
  constructor
  · exact aux _ (Finset.sum_nonneg (fun k _ => sq_nonneg _))
      (boundary_ward_row H hH d hd u z hzp hu i)
  · exact aux _ (Finset.sum_nonneg (fun k _ => sq_nonneg _))
      (boundary_ward_column H hH d hd u z hzp hu i)

/-- The standard entry estimate requires no tree or excess regularity. -/
theorem boundaryGreen_entry_norm_le (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (d : V → ℝ) (hd : ∀ k, 0 ≤ d k) (u z : ℂ)
    (hz : 0 < z.im) (hu : 0 ≤ u.im) (i j : V) :
    ‖boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z i j‖ ≤ 1 / z.im := by
  let P := boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z
  have hterm : ‖P i j‖ ^ 2 ≤ ∑ k, ‖P i k‖ ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg ‖P i k‖) (Finset.mem_univ j)
  have hsum := (boundary_square_sum_bounds H hH d hd u z z.im hz le_rfl hu i).1
  have hsquare : ‖P i j‖ ^ 2 ≤ (1 / z.im) ^ 2 := by
    apply hterm.trans
    simpa only [one_div_pow] using hsum
  change ‖P i j‖ ≤ 1 / z.im
  nlinarith [norm_nonneg (P i j), div_pos (by norm_num : (0 : ℝ) < 1) hz]

/-- Exact two-variable perturbation identity for spectral and boundary inputs. -/
theorem boundaryGreen_sub_two (H D : Matrix V V ℂ) (u v z w : ℂ)
    (hu : IsUnit (boundaryMatrix H D u z))
    (hv : IsUnit (boundaryMatrix H D v w)) :
    boundaryGreen H D u z - boundaryGreen H D v w =
      boundaryGreen H D u z * ((z - w) • 1 + (u - v) • D) * boundaryGreen H D v w := by
  unfold boundaryGreen
  rw [Matrix.inv_sub_inv ⟨fun _ => hv, fun _ => hu⟩]
  have hdiff : boundaryMatrix H D v w - boundaryMatrix H D u z =
      (z - w) • (1 : Matrix V V ℂ) + (u - v) • D := by
    simp only [boundaryMatrix, spectralMatrix, sub_smul]
    abel
  rw [hdiff]

theorem boundaryGreen_sub_two_expanded (H D : Matrix V V ℂ) (u v z w : ℂ)
    (hu : IsUnit (boundaryMatrix H D u z))
    (hv : IsUnit (boundaryMatrix H D v w)) :
    boundaryGreen H D u z - boundaryGreen H D v w =
      (z - w) • (boundaryGreen H D u z * boundaryGreen H D v w) +
      (u - v) • (boundaryGreen H D u z * D * boundaryGreen H D v w) := by
  rw [boundaryGreen_sub_two H D u v z w hu hv, Matrix.mul_add, Matrix.add_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

omit [DecidableEq V] in
/-- A finite product estimate used for both unweighted and diagonal-weighted
resolvent perturbations. -/
theorem boundary_product_sum_le (a b : V → ℂ) (R : ℝ)
    (ha : (∑ k, ‖a k‖ ^ 2) ≤ R) (hb : (∑ k, ‖b k‖ ^ 2) ≤ R) :
    (∑ k, ‖a k‖ * ‖b k‖) ≤ R := by
  calc
    (∑ k, ‖a k‖ * ‖b k‖) ≤ ∑ k, ((‖a k‖ ^ 2 + ‖b k‖ ^ 2) / 2) := by
      apply Finset.sum_le_sum
      intro k _
      nlinarith [sq_nonneg (‖a k‖ - ‖b k‖)]
    _ = ((∑ k, ‖a k‖ ^ 2) + (∑ k, ‖b k‖ ^ 2)) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ R := by linarith

/-- Coarse continuity of the actual two-variable boundary model. This bound
is for spectral transport; the order-one boundary sensitivity needed in the
final local law still requires the deeper tree/excess estimate. -/
theorem boundaryGreen_entry_lipschitz (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (d : V → ℝ) (hd : ∀ k, 0 ≤ d k) (Dmax : ℝ) (hDmax : 0 ≤ Dmax)
    (hupper : ∀ k, d k ≤ Dmax) (u v z w : ℂ) (η₀ : ℝ) (hη₀ : 0 < η₀)
    (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im) (hu : 0 ≤ u.im) (hv : 0 ≤ v.im)
    (i j : V) :
    ‖boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) u z i j -
      boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) v w i j‖ ≤
        (dist z w + Dmax * dist u v) / η₀ ^ 2 := by
  let D : Matrix V V ℂ := Matrix.diagonal (fun k => (d k : ℂ))
  let Pu := boundaryGreen H D u z
  let Pv := boundaryGreen H D v w
  have hzp : 0 < z.im := hη₀.trans_le hz
  have hwp : 0 < w.im := hη₀.trans_le hw
  have hunitu := boundaryMatrix_isUnit H hH d hd u z hzp hu
  have hunitv := boundaryMatrix_isUnit H hH d hd v w hwp hv
  have hrow : (∑ k, ‖Pu i k‖ ^ 2) ≤ 1 / η₀ ^ 2 :=
    (boundary_square_sum_bounds H hH d hd u z η₀ hη₀ hz hu i).1
  have hcol : (∑ k, ‖Pv k j‖ ^ 2) ≤ 1 / η₀ ^ 2 :=
    (boundary_square_sum_bounds H hH d hd v w η₀ hη₀ hw hv j).2
  have hproducts : (∑ k, ‖Pu i k‖ * ‖Pv k j‖) ≤ 1 / η₀ ^ 2 :=
    boundary_product_sum_le _ _ _ hrow hcol
  have hplain : ‖(Pu * Pv) i j‖ ≤ 1 / η₀ ^ 2 := by
    calc
      _ ≤ ∑ k, ‖Pu i k * Pv k j‖ := by
        simpa only [Matrix.mul_apply] using norm_sum_le Finset.univ (fun k => Pu i k * Pv k j)
      _ = ∑ k, ‖Pu i k‖ * ‖Pv k j‖ := by simp only [norm_mul]
      _ ≤ 1 / η₀ ^ 2 := hproducts
  have hweighted : ‖(Pu * D * Pv) i j‖ ≤ Dmax / η₀ ^ 2 := by
    calc
      _ ≤ ∑ k, ‖(Pu i k * (d k : ℂ)) * Pv k j‖ := by
        change ‖∑ k, (Pu * Matrix.diagonal (fun k => (d k : ℂ))) i k * Pv k j‖ ≤ _
        simp only [Matrix.mul_diagonal]
        exact norm_sum_le Finset.univ (fun k => (Pu i k * (d k : ℂ)) * Pv k j)
      _ = ∑ k, (‖Pu i k‖ * d k * ‖Pv k j‖) := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd _)]
      _ ≤ ∑ k, Dmax * (‖Pu i k‖ * ‖Pv k j‖) := by
        apply Finset.sum_le_sum
        intro k _
        calc
          ‖Pu i k‖ * d k * ‖Pv k j‖ ≤ ‖Pu i k‖ * Dmax * ‖Pv k j‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hupper k) (norm_nonneg (Pu i k)))
              (norm_nonneg (Pv k j))
          _ = Dmax * (‖Pu i k‖ * ‖Pv k j‖) := by ring
      _ = Dmax * ∑ k, ‖Pu i k‖ * ‖Pv k j‖ := (Finset.mul_sum ..).symm
      _ ≤ Dmax * (1 / η₀ ^ 2) := mul_le_mul_of_nonneg_left hproducts hDmax
      _ = Dmax / η₀ ^ 2 := by ring
  have hid := congrArg (fun M : Matrix V V ℂ => M i j)
    (boundaryGreen_sub_two_expanded H D u v z w hunitu hunitv)
  change Pu i j - Pv i j = (z - w) * (Pu * Pv) i j + (u - v) * (Pu * D * Pv) i j at hid
  change ‖Pu i j - Pv i j‖ ≤ _
  rw [hid]
  calc
    ‖(z - w) * (Pu * Pv) i j + (u - v) * (Pu * D * Pv) i j‖
        ≤ ‖(z - w) * (Pu * Pv) i j‖ + ‖(u - v) * (Pu * D * Pv) i j‖ := norm_add_le _ _
    _ = ‖z - w‖ * ‖(Pu * Pv) i j‖ + ‖u - v‖ * ‖(Pu * D * Pv) i j‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ ‖z - w‖ * (1 / η₀ ^ 2) + ‖u - v‖ * (Dmax / η₀ ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hplain (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hweighted (norm_nonneg _))
    _ = (dist z w + Dmax * dist u v) / η₀ ^ 2 := by
      rw [dist_eq_norm, dist_eq_norm]
      ring

end LocalLaw
