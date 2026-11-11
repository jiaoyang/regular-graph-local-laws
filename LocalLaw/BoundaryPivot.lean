import LocalLaw.DeficientGraphModel

/-!
# Nonzero actual finite boundary-model pivots

Strict upper-half-plane positivity follows from a nonzero solved inverse
column and the exact weighted Ward identity. No diagonal lower estimate or
reference entry bound is assumed.
-/

open scoped BigOperators
namespace LocalLaw
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem boundaryGreen_column_nonzero (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (D : V → ℝ) (hD : ∀ k, 0 ≤ D k) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (i : V) : ∃ k, boundaryGreen H (Matrix.diagonal (fun v => (D v : ℂ))) q z k i ≠ 0 := by
  classical
  let A := boundaryMatrix H (Matrix.diagonal (fun v => (D v : ℂ))) q z
  let P := boundaryGreen H (Matrix.diagonal (fun v => (D v : ℂ))) q z
  have hunit := boundaryMatrix_isUnit H hH D hD q z hz hq
  have hprod : A * P = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hunit)
  by_contra hn
  have hzero : ∀ k, P k i = 0 := by simpa only [not_exists, not_not] using hn
  have hh := congrArg (fun M : Matrix V V ℂ => M i i) hprod
  simp only [Matrix.mul_apply, hzero, mul_zero, Finset.sum_const_zero,
    Matrix.one_apply, if_pos rfl, ite_true] at hh
  exact zero_ne_one hh

theorem boundaryGreen_diagonal_im_pos (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (D : V → ℝ) (hD : ∀ k, 0 ≤ D k) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (i : V) : 0 < (boundaryGreen H (Matrix.diagonal (fun v => (D v : ℂ))) q z i i).im := by
  obtain ⟨k, hk⟩ := boundaryGreen_column_nonzero H hH D hD q z hz hq i
  have hkpos : 0 < ‖boundaryGreen H (Matrix.diagonal (fun v => (D v : ℂ))) q z k i‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hk)
  have hterm := Finset.single_le_sum
    (s := (Finset.univ : Finset V))
    (f := fun k => ‖boundaryGreen H (Matrix.diagonal (fun v => (D v : ℂ))) q z k i‖ ^ 2)
    (fun l _ => sq_nonneg _) (Finset.mem_univ k)
  have hweighted : 0 ≤ q.im * ∑ k,
      D k * ‖boundaryGreen H (Matrix.diagonal (fun v => (D v : ℂ))) q z k i‖ ^ 2 :=
    mul_nonneg hq (Finset.sum_nonneg (fun k _ => mul_nonneg (hD k) (sq_nonneg _)))
  rw [boundary_ward_column_exact H hH D hD q z hz hq i]
  exact add_pos_of_pos_of_nonneg (mul_pos hz (hkpos.trans_le hterm)) hweighted

theorem boundaryGreen_diagonal_ne_zero (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (D : V → ℝ) (hD : ∀ k, 0 ≤ D k) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (i : V) : boundaryGreen H (Matrix.diagonal (fun v => (D v : ℂ))) q z i i ≠ 0 := by
  intro hh
  have hp := boundaryGreen_diagonal_im_pos H hH D hD q z hz hq i
  rw [hh, Complex.zero_im] at hp
  exact lt_irrefl _ hp

namespace DeficientGraph
variable {d : ℕ}

theorem extensionGreen_diagonal_im_pos (g : DeficientGraph V d) (hd : 3 ≤ d)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (i : V) :
    0 < (g.extensionGreen q z i i).im :=
  boundaryGreen_diagonal_im_pos g.H (normalizedAdjacency_isHermitian g.graph d)
    g.boundaryCoefficient (g.boundaryCoefficient_nonnegative hd) q z hz hq i

theorem extensionGreen_diagonal_ne_zero (g : DeficientGraph V d) (hd : 3 ≤ d)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (i : V) :
    g.extensionGreen q z i i ≠ 0 :=
  boundaryGreen_diagonal_ne_zero g.H (normalizedAdjacency_isHermitian g.graph d)
    g.boundaryCoefficient (g.boundaryCoefficient_nonnegative hd) q z hz hq i

end DeficientGraph
end LocalLaw
