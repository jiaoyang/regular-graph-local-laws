import LocalLaw.BoundaryResolvent

/-!
# Genuine inverses for nonuniform Herglotz diagonal self-energies

Separating real and imaginary diagonal parts reduces this case to the proved
Hermitian dissipative boundary inverse theorem. This applies to the ordinary
component self-energies in the localization Schur complement.
-/

noncomputable section
namespace LocalLaw
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem complex_diagonal_spectral_isUnit (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (e : V → ℂ) (he : ∀ v, 0 ≤ (e v).im) (z : ℂ) (hz : 0 < z.im) :
    IsUnit (spectralMatrix H z - Matrix.diagonal e) := by
  let Hreal := H - Matrix.diagonal (fun v => ((e v).re : ℂ))
  have hreal : Hreal.IsHermitian := by
    apply hH.sub
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro v
    simp [isSelfAdjoint_iff]
  have hunit := boundaryMatrix_isUnit Hreal hreal (fun v => (e v).im) he Complex.I z hz (by norm_num)
  have hid : spectralMatrix H z - Matrix.diagonal e =
      boundaryMatrix Hreal (Matrix.diagonal (fun v => ((e v).im : ℂ))) Complex.I z := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [boundaryMatrix, Hreal, spectralMatrix, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul, Matrix.diagonal_apply_eq, Matrix.one_apply_eq, mul_one]
      rw [← Complex.re_add_im (e i)]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
        Complex.add_im, Complex.mul_im, zero_add, mul_one]
      ring
    · simp [boundaryMatrix, Hreal, spectralMatrix, Matrix.diagonal_apply, Matrix.one_apply, hij]
  rw [hid]
  exact hunit

end LocalLaw
