import LocalLaw.FiniteModel

/-!
# A finite constant eigenvector forbids a uniform resolvent bound

This supplies the obstruction needed to bound a reference threshold: a finite
closed regular component has a real eigenvalue, so its resolvent entries
cannot remain uniformly bounded as the imaginary part approaches zero.
-/

open scoped BigOperators
namespace LocalLaw

section
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual inverse preserves the constant-vector eigenvalue equation. -/
theorem green_constant_row_sum (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (eig : ℝ) (hrow : ∀ i, ∑ j, H i j = (eig : ℂ)) (z : ℂ) (hz : 0 < z.im) (i : V) :
    (∑ j, green H z i j) * ((eig : ℂ) - z) = 1 := by
  classical
  have hB : ∀ k, ∑ j, spectralMatrix H z k j = (eig : ℂ) - z := by
    intro k
    simp only [spectralMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
    rw [hrow k]
    simp
  have hprod := green_mul_spectralMatrix H hH z hz
  have hsum := congrArg (fun A : Matrix V V ℂ => ∑ j, A i j) hprod
  simp only [Matrix.mul_apply, Matrix.one_apply] at hsum
  rw [Finset.sum_comm] at hsum
  simp_rw [← Finset.mul_sum, hB] at hsum
  rw [← Finset.sum_mul] at hsum
  simpa using hsum

/-- For every proposed constant C, some upper-half-plane entry exceeds C
inside the fixed disk of radius |lambda|+1. No limit argument is assumed. -/
theorem resolvent_entries_unbounded_near_constant_eigenvalue [Nonempty V]
    (H : Matrix V V ℂ) (hH : H.IsHermitian) (eig : ℝ)
    (hrow : ∀ i, ∑ j, H i j = (eig : ℂ)) (C : ℝ) :
    ∃ z : ℂ, 0 < z.im ∧ ‖z‖ ≤ |eig| + 1 ∧ ∃ i j, C < ‖green H z i j‖ := by
  classical
  let n : ℝ := Fintype.card V
  let η : ℝ := 1 / (n * (|C| + 1) + 1)
  let z : ℂ := (eig : ℂ) + (η : ℂ) * Complex.I
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hden : 0 < n * (|C| + 1) + 1 := by positivity
  have hη : 0 < η := div_pos (by norm_num) hden
  have hηone : η ≤ 1 := (div_le_one hden).mpr (by nlinarith [abs_nonneg C])
  have hz : 0 < z.im := by simpa only [z, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using hη
  have hznorm : ‖z‖ ≤ |eig| + 1 := by
    calc
      ‖z‖ ≤ ‖(eig : ℂ)‖ + ‖(η : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |eig| + η := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one, abs_of_pos hη]
      _ ≤ |eig| + 1 := by linarith
  refine ⟨z, hz, hznorm, ?_⟩
  by_contra hnone
  push_neg at hnone
  let i : V := Classical.choice inferInstance
  have hsum : ‖∑ j, green H z i j‖ ≤ n * |C| := by
    calc
      _ ≤ ∑ j, ‖green H z i j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : V, |C| := Finset.sum_le_sum (fun j _ => (hnone i j).trans (le_abs_self C))
      _ = n * |C| := by simp [n, nsmul_eq_mul]
  have hid := green_constant_row_sum H hH eig hrow z hz i
  have hfactor : ‖(eig : ℂ) - z‖ = η := by
    have heq : (eig : ℂ) - z = -(η : ℂ) * Complex.I := by dsimp [z]; ring
    rw [heq, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hη, Complex.norm_I, mul_one]
  have hnorm := congrArg norm hid
  rw [norm_mul, norm_one, hfactor] at hnorm
  have hle : (1 : ℝ) ≤ η * (n * |C|) := by nlinarith [mul_le_mul_of_nonneg_right hsum hη.le]
  have hstrict : η * (n * |C|) < 1 := by
    dsimp [η]
    rw [one_div_mul_eq_div]
    apply (div_lt_one hden).mpr
    nlinarith
  linarith

end
end LocalLaw
