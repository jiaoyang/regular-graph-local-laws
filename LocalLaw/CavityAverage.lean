import LocalLaw.Resolvent

/-!
# The actual cavity average is a mean over centers

The deleted-vertex indexing is extended by zero on the deleted vertex, then
finite sums are interchanged. This connects the concrete Q of the regular
 graph model to the averaging hypothesis used by the local certificate proof.
-/

open scoped BigOperators

namespace LocalLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An oriented-edge cavity term, extended by zero on nonedges and on i=j. -/
noncomputable def orientedCavity (G : SimpleGraph V) (d : ℕ) (z : ℂ) (i j : V) : ℂ := by
  classical
  exact if h : i ≠ j then
    if G.Adj i j then
      green (deletedMatrix (normalizedAdjacency G d) j) z ⟨i, h⟩ ⟨i, h⟩ else 0
    else 0

/-- Neighbor-averaged cavity value at a center. -/
noncomputable def cavityAtVertex (G : SimpleGraph V) (d : ℕ) (z : ℂ) (i : V) : ℂ :=
  (d : ℂ)⁻¹ * ∑ j, orientedCavity G d z i j

private theorem orientedCavity_sum_deleted (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (z : ℂ) (j : V) :
    (∑ i : {i : V // i ≠ j},
      if G.Adj i.val j then green (deletedMatrix (normalizedAdjacency G d) j) z i i else 0) =
    ∑ i, orientedCavity G d z i j := by
  classical
  have hfirst : (∑ i : {i : V // i ≠ j},
      if G.Adj i.val j then green (deletedMatrix (normalizedAdjacency G d) j) z i i else 0) =
      ∑ i : {i : V // i ≠ j}, orientedCavity G d z i.val j := by
    apply Finset.sum_congr rfl
    intro i _
    rcases i with ⟨i, hi⟩
    by_cases ha : G.Adj i j <;> simp [orientedCavity, hi, ha]
  rw [hfirst]
  have hzero : (∑ i : {i : V // ¬ i ≠ j}, orientedCavity G d z i.val j) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : i.val = j := not_ne_iff.mp i.property
    simp [orientedCavity, hi]
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i : V => i ≠ j)
    (fun i => orientedCavity G d z i j)
  simpa only [hzero, add_zero] using hsplit

/-- Concrete oriented-edge average equals the mean of centered cavity values. -/
theorem cavityAverage_eq_mean (G : SimpleGraph V) (d : ℕ) (z : ℂ) :
    cavityAverage G d z =
      (Fintype.card V : ℝ)⁻¹ • ∑ i, cavityAtVertex G d z i := by
  classical
  unfold cavityAverage cavityAtVertex
  simp_rw [orientedCavity_sum_deleted]
  rw [Finset.sum_comm, ← Finset.mul_sum]
  simp only [mul_inv_rev, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
  ring

/-- Every oriented cavity term has nonnegative imaginary part. -/
theorem orientedCavity_im_nonneg (G : SimpleGraph V) (d : ℕ) (z : ℂ)
    (hz : 0 < z.im) (i j : V) : 0 ≤ (orientedCavity G d z i j).im := by
  classical
  unfold orientedCavity
  split_ifs with hij hadj
  · exact green_diagonal_im_nonneg _
      (deletedMatrix_isHermitian _ (normalizedAdjacency_isHermitian G d) j) z hz _
  all_goals simp

/-- Centered cavity values lie in the closed upper half-plane. -/
theorem cavityAtVertex_im_nonneg (G : SimpleGraph V) (d : ℕ) (z : ℂ)
    (hz : 0 < z.im) (i : V) : 0 ≤ (cavityAtVertex G d z i).im := by
  classical
  have hcoef : (d : ℂ)⁻¹ = (↑((d : ℝ)⁻¹) : ℂ) := by push_cast; rfl
  unfold cavityAtVertex
  rw [hcoef]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  apply mul_nonneg
  · positivity
  · rw [Complex.im_sum]
    exact Finset.sum_nonneg (fun j _ => orientedCavity_im_nonneg G d z hz i j)

end LocalLaw
