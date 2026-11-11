import SpectralConsequences.SortedHermitianSpectrum
import LocalLaw.FiniteModel

/-! # Actual finite resolvents as indexed Stieltjes and Poisson sums -/

open scoped BigOperators
open Matrix
noncomputable section
namespace SpectralConsequences
open LocalLaw
variable {N : ℕ}

def finiteStieltjes (values : Fin N → ℝ) (z : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ i, ((values i : ℂ) - z)⁻¹

theorem real_sub_complex_ne_zero (x : ℝ) (z : ℂ) (hz : 0 < z.im) :
    (x : ℂ) - z ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub, neg_eq_zero] at hi
  exact hz.ne' hi

/-- The inverse is the genuine spectral conjugate; nonsingularity is proved. -/
theorem green_spectral_decomposition (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    green H z = (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) *
      Matrix.diagonal (fun i => ((hH.eigenvalues i : ℂ) - z)⁻¹) *
      star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) := by
  let U : Matrix (Fin N) (Fin N) ℂ := hH.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ) - z)
  let Di := Matrix.diagonal (fun i => ((hH.eigenvalues i : ℂ) - z)⁻¹)
  have hstar : star U * U = 1 := unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hustar : U * star U = 1 := unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hD : D = Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) - z • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [D, Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hspec : spectralMatrix H z = U * D * star U := by
    rw [hD]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hustar]
    exact congrArg (fun A => A - z • 1) hH.spectral_theorem
  have hdiag : Di * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [real_sub_complex_ne_zero _ z hz]
    · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hcand : (U * Di * star U) * spectralMatrix H z = 1 := by
    rw [hspec]
    calc
      _ = U * Di * (star U * U) * D * star U := by simp only [Matrix.mul_assoc]
      _ = U * (Di * D) * star U := by rw [hstar]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hdiag, Matrix.mul_one, hustar]
  have hh := congrArg (fun A => A * green H z) hcand
  change (U * Di * star U) * spectralMatrix H z * green H z = 1 * green H z at hh
  rw [Matrix.mul_assoc (U * Di * star U), spectralMatrix_mul_green H hH z hz,
    Matrix.mul_one, Matrix.one_mul] at hh
  exact hh.symm

theorem trace_green_eq_sum_eigenvalues (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    Matrix.trace (green H z) = ∑ i, ((hH.eigenvalues i : ℂ) - z)⁻¹ := by
  rw [green_spectral_decomposition H hH z hz, Matrix.trace_mul_cycle,
    unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]

theorem empiricalTransform_eq_finiteStieltjes (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    empiricalTransform H z = finiteStieltjes (sortedEigenvalues hH) z := by
  rw [empiricalTransform, trace_green_eq_sum_eigenvalues H hH z hz]
  simp only [Fintype.card_fin, finiteStieltjes,
    sum_sortedEigenvalues hH (fun x => ((x : ℂ) - z)⁻¹)]

theorem inverse_real_sub_im (x E η : ℝ) :
    (((x : ℂ) - ((E : ℂ) + (η : ℂ) * Complex.I))⁻¹).im =
      η / ((x - E)^2 + η^2) := by
  rw [Complex.inv_im]
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero,
    zero_add, zero_sub, neg_neg, Complex.normSq_apply, Complex.sub_re,
    Complex.add_re, Complex.mul_re, sub_zero]
  ring

/-- The normalized empirical imaginary part is exactly the positive Poisson sum. -/
theorem finiteStieltjes_im (values : Fin N → ℝ) (E η : ℝ) :
    (finiteStieltjes values ((E : ℂ) + (η : ℂ) * Complex.I)).im =
      (N : ℝ)⁻¹ * ∑ i, η / ((values i - E)^2 + η^2) := by
  unfold finiteStieltjes
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add,
    Complex.im_sum, inverse_real_sub_im, add_zero]

theorem finiteStieltjes_im_nonnegative (values : Fin N → ℝ) (E η : ℝ)
    (hη : 0 ≤ η) :
    0 ≤ (finiteStieltjes values ((E : ℂ) + (η : ℂ) * Complex.I)).im := by
  rw [finiteStieltjes_im]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun _ _ => div_nonneg hη (by positivity)))

end SpectralConsequences
