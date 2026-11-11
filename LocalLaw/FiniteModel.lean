import Mathlib

/-!
# Finite resolvents and boundary models

The matrix model is equation (2.11) of Huang--Yau. All inverses used in
identities have explicit nonsingularity hypotheses. Hermitian resolvents in
the open upper half-plane are proved nonsingular using the real spectrum.
-/

open scoped BigOperators

set_option maxHeartbeats 800000

namespace LocalLaw

section FiniteMatrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The sign convention in the paper is H-zI. -/
def spectralMatrix (H : Matrix V V ℂ) (z : ℂ) : Matrix V V ℂ := H - z • 1

noncomputable def green (H : Matrix V V ℂ) (z : ℂ) : Matrix V V ℂ :=
  (spectralMatrix H z)⁻¹

/-- The diagonal boundary self energy is subtracted from H-zI. -/
def boundaryMatrix (H D : Matrix V V ℂ) (w z : ℂ) : Matrix V V ℂ :=
  spectralMatrix H z - w • D

noncomputable def boundaryGreen (H D : Matrix V V ℂ) (w z : ℂ) : Matrix V V ℂ :=
  (boundaryMatrix H D w z)⁻¹

/-- No totalized inverse is mistaken for an inverse: the determinant is a unit. -/
theorem spectralMatrix_isUnit_of_im_ne_zero (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) : IsUnit (spectralMatrix H z) := by
  have hzspec : z ∉ spectrum ℂ H := by
    intro h
    rw [hH.spectral_theorem, unitary.spectrum.unitary_conjugate, spectrum_diagonal] at h
    obtain ⟨i, hi⟩ := h
    have heq := congrArg Complex.im hi
    change (0 : ℝ) = z.im at heq
    exact hz heq.symm
  have hu := (spectrum.not_mem_iff.mp hzspec).neg
  simpa [spectralMatrix, Algebra.algebraMap_eq_smul_one] using hu

theorem spectralMatrix_isUnit (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) : IsUnit (spectralMatrix H z) :=
  spectralMatrix_isUnit_of_im_ne_zero H hH z (ne_of_gt hz)

theorem green_mul_spectralMatrix (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) : green H z * spectralMatrix H z = 1 := by
  exact Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (spectralMatrix_isUnit H hH z hz))

theorem spectralMatrix_mul_green (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) : spectralMatrix H z * green H z = 1 := by
  exact Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (spectralMatrix_isUnit H hH z hz))

/-- The first resolvent identity with the paper's sign convention. -/
theorem green_sub_green_of_im_ne_zero (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    green H z - green H w = (z - w) • (green H z * green H w) := by
  have hu : IsUnit (spectralMatrix H z) ↔ IsUnit (spectralMatrix H w) :=
    ⟨fun _ => spectralMatrix_isUnit_of_im_ne_zero H hH w hw,
     fun _ => spectralMatrix_isUnit_of_im_ne_zero H hH z hz⟩
  unfold green
  rw [Matrix.inv_sub_inv hu]
  have hdiff : spectralMatrix H w - spectralMatrix H z = (z - w) • (1 : Matrix V V ℂ) := by
    simp only [spectralMatrix, sub_smul]
    abel
  rw [hdiff, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

theorem green_sub_green (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z w : ℂ) (hz : 0 < z.im) (hw : 0 < w.im) :
    green H z - green H w = (z - w) • (green H z * green H w) :=
  green_sub_green_of_im_ne_zero H hH z w (ne_of_gt hz) (ne_of_gt hw)

/-- Conjugating the spectral parameter gives the adjoint resolvent. -/
theorem green_conjTranspose (H : Matrix V V ℂ) (hH : H.IsHermitian) (z : ℂ) :
    (green H z).conjTranspose = green H (starRingEnd ℂ z) := by
  unfold green
  rw [Matrix.conjTranspose_nonsing_inv]
  congr 1
  simp only [spectralMatrix, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, hH.eq]
  rfl

/-- Matrix form of Ward's identity. -/
theorem green_sub_adjoint (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    green H z - (green H z).conjTranspose =
      (z - starRingEnd ℂ z) • (green H z * (green H z).conjTranspose) := by
  rw [green_conjTranspose H hH]
  apply green_sub_green_of_im_ne_zero H hH z (starRingEnd ℂ z) hz
  simpa only [Complex.conj_im, neg_ne_zero] using hz

/-- Ward's identity for one row, including the exact factor Im(z). -/
theorem ward_identity (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (i : V) :
    ∑ k, ‖green H z i k‖ ^ 2 = (green H z i i).im / z.im := by
  have hid := congrArg (fun M : Matrix V V ℂ => (M i i).im)
    (green_sub_adjoint H hH z (ne_of_gt hz))
  have hsum : (green H z * (green H z).conjTranspose) i i =
      (↑(∑ k, ‖green H z i k‖ ^ 2) : ℂ) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, starRingEnd_apply,
      ← Complex.mul_conj', Complex.ofReal_sum, Complex.ofReal_pow]
  change ((green H z i i) - starRingEnd ℂ (green H z i i)).im =
    ((z - starRingEnd ℂ z) * (green H z * (green H z).conjTranspose) i i).im at hid
  rw [hsum, Complex.sub_conj] at hid
  simp only [Complex.sub_im, Complex.conj_im, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one] at hid
  apply (eq_div_iff (ne_of_gt hz)).2
  nlinarith

/-- Exact perturbation identity for the boundary weight. -/
theorem boundaryGreen_sub (H D : Matrix V V ℂ) (u v z : ℂ)
    (hu : IsUnit (boundaryMatrix H D u z))
    (hv : IsUnit (boundaryMatrix H D v z)) :
    boundaryGreen H D u z - boundaryGreen H D v z =
      (u - v) • (boundaryGreen H D u z * D * boundaryGreen H D v z) := by
  unfold boundaryGreen
  rw [Matrix.inv_sub_inv ⟨fun _ => hv, fun _ => hu⟩]
  have hdiff : boundaryMatrix H D v z - boundaryMatrix H D u z = (u - v) • D := by
    simp only [boundaryMatrix, sub_smul]
    abel
  rw [hdiff, Matrix.mul_smul, Matrix.smul_mul]

/-- Finite weighted boundary sensitivity, before any tree estimates. -/
theorem boundaryGreen_entry_bound (H : Matrix V V ℂ) (d : V → ℂ) (u v z : ℂ)
    (hu : IsUnit (boundaryMatrix H (Matrix.diagonal d) u z))
    (hv : IsUnit (boundaryMatrix H (Matrix.diagonal d) v z)) (i j : V) :
    ‖boundaryGreen H (Matrix.diagonal d) u z i j -
      boundaryGreen H (Matrix.diagonal d) v z i j‖ ≤
      ‖u - v‖ * ∑ k, (‖boundaryGreen H (Matrix.diagonal d) u z i k‖ * ‖d k‖ *
        ‖boundaryGreen H (Matrix.diagonal d) v z k j‖) := by
  have hid := congrFun (congrFun (boundaryGreen_sub H (Matrix.diagonal d) u v z hu hv) i) j
  change boundaryGreen H (Matrix.diagonal d) u z i j -
      boundaryGreen H (Matrix.diagonal d) v z i j =
    (u - v) * (boundaryGreen H (Matrix.diagonal d) u z * Matrix.diagonal d *
      boundaryGreen H (Matrix.diagonal d) v z) i j at hid
  rw [hid, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  simpa only [norm_mul] using
    (norm_sum_le (Finset.univ) (fun k =>
      (boundaryGreen H (Matrix.diagonal d) u z i k * d k) *
      boundaryGreen H (Matrix.diagonal d) v z k j))

/-- A bound on the weighted product sum yields the boundary Lipschitz bound
needed by the final local law. -/
theorem boundaryGreen_entry_sensitivity (H : Matrix V V ℂ) (d : V → ℂ) (u v z : ℂ)
    (hu : IsUnit (boundaryMatrix H (Matrix.diagonal d) u z))
    (hv : IsUnit (boundaryMatrix H (Matrix.diagonal d) v z)) (i j : V) (K : ℝ)
    (hsum : (∑ k, (‖boundaryGreen H (Matrix.diagonal d) u z i k‖ * ‖d k‖ *
      ‖boundaryGreen H (Matrix.diagonal d) v z k j‖)) ≤ K) :
    ‖boundaryGreen H (Matrix.diagonal d) u z i j -
      boundaryGreen H (Matrix.diagonal d) v z i j‖ ≤ K * dist u v := by
  calc
    _ ≤ ‖u - v‖ * ∑ k, (‖boundaryGreen H (Matrix.diagonal d) u z i k‖ * ‖d k‖ *
      ‖boundaryGreen H (Matrix.diagonal d) v z k j‖) :=
      boundaryGreen_entry_bound H d u v z hu hv i j
    _ ≤ ‖u - v‖ * K := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = K * dist u v := by rw [dist_eq_norm]; ring

/-- The average diagonal is the normalized trace, with its positive
cardinality hypothesis kept separate wherever division is estimated. -/
noncomputable def empiricalTransform (H : Matrix V V ℂ) (z : ℂ) : ℂ :=
  (Fintype.card V : ℂ)⁻¹ * Matrix.trace (green H z)

end FiniteMatrix

section GraphDefinitions
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A real scalar multiple of the adjacency matrix with normalization
1/sqrt(d-1). This remains a defined matrix for every d; graph applications
supply d≥3. -/
noncomputable def normalizedAdjacency (G : SimpleGraph V) (d : ℕ) : Matrix V V ℂ := by
  classical
  exact (↑((Real.sqrt ((d : ℝ) - 1))⁻¹) : ℂ) • G.adjMatrix ℂ

omit [Fintype V] [DecidableEq V] in
theorem normalizedAdjacency_isHermitian (G : SimpleGraph V) (d : ℕ) :
    (normalizedAdjacency G d).IsHermitian := by
  classical
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [normalizedAdjacency, Matrix.smul_apply, smul_eq_mul, star_mul,
    starRingEnd_apply, Complex.conj_ofReal]
  simp only [SimpleGraph.adjMatrix_apply]
  rw [show (G.Adj j i) = (G.Adj i j) from propext (G.adj_comm j i)]
  split_ifs <;> simp

/-- Principal submatrix after deleting j, indexed by the actual remaining
vertices, rather than a zero-padded matrix. -/
def deletedMatrix (H : Matrix V V ℂ) (j : V) : Matrix {i : V // i ≠ j} {i : V // i ≠ j} ℂ :=
  H.submatrix Subtype.val Subtype.val

omit [Fintype V] [DecidableEq V] in
theorem deletedMatrix_isHermitian (H : Matrix V V ℂ) (hH : H.IsHermitian) (j : V) :
    (deletedMatrix H j).IsHermitian := hH.submatrix _

noncomputable def cavityAverage (G : SimpleGraph V) (d : ℕ) (z : ℂ) : ℂ := by
  classical
  exact ((Fintype.card V : ℂ) * (d : ℂ))⁻¹ *
    ∑ j : V, ∑ i : {i : V // i ≠ j},
      if G.Adj i.val j then green (deletedMatrix (normalizedAdjacency G d) j) z i i else 0

/-- The deficit convention and the factor 1/(d-1) in equation (2.11). -/
noncomputable def boundaryDeficitMatrix (d : ℕ) (deficit degree : V → ℕ) : Matrix V V ℂ :=
  Matrix.diagonal (fun i =>
    (↑(((d : ℝ) - (deficit i : ℝ) - (degree i : ℝ)) / ((d : ℝ) - 1)) : ℂ))

end GraphDefinitions

end LocalLaw
