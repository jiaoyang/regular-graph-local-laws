import LocalLaw.MinorIdentity

/-!
# Averaged resolvent perturbation from actual Ward identities

The comparison uses the total entry mass of the matrix perturbation and the
actual imaginary-part caps. A finite nonnegative weight matrix permits both
the diagonal average and regular-graph edge averages as special cases.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance comparisonWardDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact change-of-matrix resolvent identity with genuine inverse units. -/
theorem green_matrix_difference (H K : Matrix V V ℂ) (hH : H.IsHermitian)
    (hK : K.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    green H z - green K z = green H z * (K - H) * green K z := by
  have hu : IsUnit (spectralMatrix H z) ↔ IsUnit (spectralMatrix K z) :=
    ⟨fun _ => spectralMatrix_isUnit K hK z hz, fun _ => spectralMatrix_isUnit H hH z hz⟩
  unfold green
  rw [Matrix.inv_sub_inv hu]
  congr 2
  unfold spectralMatrix
  abel

/-- Young's inequality and the exact row/column Ward sums bound an arbitrary
regular nonnegative weighted product; no independence is used. -/
theorem weighted_green_product_ward (H K : Matrix V V ℂ) (hH : H.IsHermitian)
    (hK : K.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (W : Matrix V V ℝ) (D : ℝ) (hW : ∀ i j, 0 ≤ W i j)
    (hrow : ∀ i, ∑ j, W i j = D) (hcol : ∀ j, ∑ i, W i j = D) (u v : V) :
    (∑ i, ∑ j, W i j * ‖green H z i u‖ * ‖green K z v j‖) ≤
      D * ((green H z u u).im + (green K z v v).im) / (2 * z.im) := by
  calc
    _ ≤ ∑ i, ∑ j, W i j * (‖green H z i u‖ ^ 2 + ‖green K z v j‖ ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have h := mul_nonneg (hW i j) (sq_nonneg (‖green H z i u‖ - ‖green K z v j‖))
      nlinarith
    _ = (D * (∑ i, ‖green H z i u‖ ^ 2) + D * (∑ j, ‖green K z v j‖ ^ 2)) / 2 := by
      simp_rw [mul_add, add_div, Finset.sum_add_distrib]
      congr 1
      · simp_rw [← Finset.sum_div, ← Finset.sum_mul, hrow]
        rw [← Finset.mul_sum]
      · rw [Finset.sum_comm]
        simp_rw [← Finset.sum_div, ← Finset.sum_mul, hcol]
        rw [← Finset.mul_sum]
    _ = _ := by
      rw [ward_identity_column H hH z hz u, ward_identity K hK z hz v]
      ring

/-- A genuine matrix perturbation controls the weighted mean absolute entry
change by its total entry mass and the diagonal imaginary-part cap. -/
theorem weighted_green_difference_ward (H K : Matrix V V ℂ) (hH : H.IsHermitian)
    (hK : K.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (W : Matrix V V ℝ) (D I : ℝ) (hW : ∀ i j, 0 ≤ W i j) (hD : 0 ≤ D)
    (hrow : ∀ i, ∑ j, W i j = D) (hcol : ∀ j, ∑ i, W i j = D)
    (hHI : ∀ u, (green H z u u).im ≤ I) (hKI : ∀ v, (green K z v v).im ≤ I) :
    (∑ i, ∑ j, W i j * ‖green H z i j - green K z i j‖) ≤
      (D * I / z.im) * (∑ u, ∑ v, ‖(K - H) u v‖) := by
  have hentry : ∀ i j, ‖green H z i j - green K z i j‖ ≤
      ∑ u, ∑ v, ‖green H z i u‖ * ‖(K - H) u v‖ * ‖green K z v j‖ := by
    intro i j
    have hid := congrArg (fun M : Matrix V V ℂ => M i j) (green_matrix_difference H K hH hK z hz)
    change green H z i j - green K z i j = (green H z * (K - H) * green K z) i j at hid
    rw [hid, Matrix.mul_assoc, Matrix.mul_apply]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro u _
    rw [norm_mul, Matrix.mul_apply]
    calc
      _ ≤ ‖green H z i u‖ * ∑ v, ‖(K - H) u v * green K z v j‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
      _ = _ := by simp_rw [Finset.mul_sum, norm_mul]; ring
  calc
    _ ≤ ∑ i, ∑ j, W i j * (∑ u, ∑ v,
        ‖green H z i u‖ * ‖(K - H) u v‖ * ‖green K z v j‖) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hentry i j) (hW i j)
    _ = ∑ u, ∑ v, ‖(K - H) u v‖ *
        (∑ i, ∑ j, W i j * ‖green H z i u‖ * ‖green K z v j‖) := by
      simp_rw [Finset.mul_sum]
      conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ u, ∑ v, ‖(K - H) u v‖ * (D * I / z.im) := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro v _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hp := weighted_green_product_ward H K hH hK z hz W D hW hrow hcol u v
      apply hp.trans
      apply (div_le_iff₀ (by positivity : 0 < 2 * z.im)).mpr
      have hh := mul_le_mul_of_nonneg_left (add_le_add (hHI u) (hKI v)) hD
      calc
        D * ((green H z u u).im + (green K z v v).im) ≤ D * (I + I) := hh
        _ = (D * I / z.im) * (2 * z.im) := by field_simp; ring
    _ = _ := by simp_rw [← Finset.sum_mul]; ring

/-- The diagonal L1 change is the identity-weight specialization. -/
theorem diagonal_green_difference_ward (H K : Matrix V V ℂ) (hH : H.IsHermitian)
    (hK : K.IsHermitian) (z : ℂ) (hz : 0 < z.im) (I : ℝ)
    (hHI : ∀ u, (green H z u u).im ≤ I) (hKI : ∀ v, (green K z v v).im ≤ I) :
    (∑ i, ‖green H z i i - green K z i i‖) ≤
      (I / z.im) * (∑ u, ∑ v, ‖(K - H) u v‖) := by
  simpa only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true] using
    weighted_green_difference_ward H K hH hK z hz (1 : Matrix V V ℝ) 1 I
      (by intro i j; simp only [Matrix.one_apply]; split_ifs <;> norm_num)
      (by norm_num) (by intro i; simp [Matrix.one_apply])
      (by intro j; simp [Matrix.one_apply]) hHI hKI

/-- Exact degree marginals specialize the weighted comparison to all
oriented graph edges, with the same sharp imaginary-part factor. -/
theorem regular_edge_green_difference_ward (G : SimpleGraph V) (d : ℕ)
    (hregular : G.IsRegularOfDegree d)
    (H K : Matrix V V ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (I : ℝ)
    (hHI : ∀ u, (green H z u u).im ≤ I) (hKI : ∀ v, (green K z v v).im ≤ I) :
    (∑ i, ∑ j, if G.Adj i j then ‖green H z i j - green K z i j‖ else 0) ≤
      ((d : ℝ) * I / z.im) * (∑ u, ∑ v, ‖(K - H) u v‖) := by
  let W : Matrix V V ℝ := fun i j => if G.Adj i j then 1 else 0
  have hrow : ∀ i, ∑ j, W i j = (d : ℝ) := by
    intro i
    dsimp only [W]
    rw [← G.degree_eq_sum_if_adj (R := ℝ)]
    have hh := hregular i
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh ⊢
    exact_mod_cast hh
  have hcol : ∀ j, ∑ i, W i j = (d : ℝ) := by
    intro j
    simpa only [W, G.adj_comm] using hrow j
  simpa only [W, ite_mul, one_mul, zero_mul] using
    weighted_green_difference_ward H K hH hK z hz W (d : ℝ) I
      (by intro i j; dsimp only [W]; split_ifs <;> norm_num)
      (Nat.cast_nonneg d) hrow hcol hHI hKI

end
end LocalLaw
