import LocalLaw.Resolvent

/-!
# Strict positivity and the actual one-vertex resolvent identity

The denominator G_jj is proved nonzero from Ward and the matrix inverse
identity. The deleted matrix is indexed by the subtype {i // i != j}; the
single-vertex Schur identity is derived from an actual left inverse.
-/

open scoped BigOperators

namespace LocalLaw

section Positivity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A resolvent column cannot vanish because its product with the spectral
matrix is the corresponding column of the identity. -/
theorem green_column_nonzero (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (i : V) : ∃ k, green H z k i ≠ 0 := by
  classical
  by_contra hn
  have hzero : ∀ k, green H z k i = 0 := by simpa using hn
  have hid := congrArg (fun M : Matrix V V ℂ => M i i)
    (spectralMatrix_mul_green H hH z hz)
  simp only [Matrix.mul_apply, hzero, mul_zero, Finset.sum_const_zero,
    Matrix.one_apply, if_true] at hid
  exact zero_ne_one hid

/-- Strict positivity, including for every vertex-deleted Hermitian matrix. -/
theorem green_diagonal_im_pos (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (i : V) : 0 < (green H z i i).im := by
  obtain ⟨k, hk⟩ := green_column_nonzero H hH z hz i
  have ht : 0 < ‖green H z k i‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hk)
  have hterm : ‖green H z k i‖ ^ 2 ≤ ∑ l, ‖green H z l i‖ ^ 2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg ‖green H z l i‖) (Finset.mem_univ k)
  have hsum : 0 < ∑ l, ‖green H z l i‖ ^ 2 := ht.trans_le hterm
  rw [ward_identity_column H hH z hz i] at hsum
  exact (div_pos_iff_of_pos_right hz).mp hsum

theorem green_diagonal_ne_zero (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (i : V) : green H z i i ≠ 0 := by
  intro heq
  have hp := green_diagonal_im_pos H hH z hz i
  rw [heq, Complex.zero_im] at hp
  exact lt_irrefl _ hp

end Positivity

section MatrixDeletion

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Extending a deleted-index sum by a zero term recovers the full sum. -/
theorem sum_deleted_eq_sum_of_zero {E : Type*} [AddCommMonoid E]
    (j : V) (f : V → E) (hj : f j = 0) :
    (∑ k : {k : V // k ≠ j}, f k) = ∑ k : V, f k := by
  classical
  calc
    (∑ k : {k : V // k ≠ j}, f k) = ∑ k ∈ Finset.univ.erase j, f k :=
      (Finset.sum_subtype (Finset.univ.erase j) (by simp [ne_comm]) f).symm
    _ = ∑ k : V, f k := Finset.sum_erase _ hj

/-- The correction matrix indexed by the actual remaining vertices. -/
noncomputable def deletionInverseCandidate (C : Matrix V V ℂ) (j : V) :
    Matrix {i : V // i ≠ j} {i : V // i ≠ j} ℂ :=
  fun i k => C i k - C i j * C j k / C j j

/-- Algebraic deletion identity. An explicit left inverse and a nonzero pivot
are sufficient; no totalized inverse is used as if it were nonsingular. -/
theorem deleted_matrix_inverse (A C : Matrix V V ℂ) (j : V)
    (hleft : C * A = 1) (hpivot : C j j ≠ 0) :
    (A.submatrix Subtype.val Subtype.val)⁻¹ = deletionInverseCandidate C j := by
  classical
  apply Matrix.inv_eq_left_inv
  ext i l
  change (∑ k : {k : V // k ≠ j},
    (C i k - C i j * C j k / C j j) * A k l) =
      (1 : Matrix {i : V // i ≠ j} {i : V // i ≠ j} ℂ) i l
  have hz : (C i j - C i j * C j j / C j j) * A j l = 0 := by
    simp [hpivot]
  let f : V → ℂ := fun k => (C i k - C i j * C j k / C j j) * A k l
  change (∑ k : {k : V // k ≠ j}, f k) = _
  rw [sum_deleted_eq_sum_of_zero j f hz]
  dsimp only [f]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  have hfactor : (∑ k : V, (C i j * C j k / C j j) * A k l) =
      (C i j / C j j) * ∑ k : V, C j k * A k l := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hfactor]
  change (C * A) i l - (C i j / C j j) * (C * A) j l = _
  rw [hleft]
  simp only [Matrix.one_apply]
  have hjl : j ≠ (l : V) := Ne.symm l.property
  rw [if_neg hjl, mul_zero, sub_zero]
  congr 1
  exact propext Subtype.coe_inj

omit [Fintype V] in
/-- Spectral shifting commutes with genuine vertex deletion. -/
theorem spectralMatrix_deleted (H : Matrix V V ℂ) (z : ℂ) (j : V) :
    spectralMatrix (deletedMatrix H j) z =
      (spectralMatrix H z).submatrix Subtype.val Subtype.val := by
  ext i k
  simp [spectralMatrix, deletedMatrix, Matrix.one_apply, Subtype.ext_iff]

/-- The actual one-vertex Green-function identity (A.4), with its denominator
and subtype-indexing obligations discharged. -/
theorem green_deleted_vertex (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (j : V)
    (i k : {i : V // i ≠ j}) :
    green (deletedMatrix H j) z i k =
      green H z i k - green H z i j * green H z j k / green H z j j := by
  have hid := deleted_matrix_inverse (spectralMatrix H z) (green H z) j
    (green_mul_spectralMatrix H hH z hz) (green_diagonal_ne_zero H hH z hz j)
  have hentry := congrArg (fun M : Matrix {i : V // i ≠ j} {i : V // i ≠ j} ℂ => M i k) hid
  change (spectralMatrix (deletedMatrix H j) z)⁻¹ i k = _
  rw [spectralMatrix_deleted]
  exact hentry

end MatrixDeletion

end LocalLaw
