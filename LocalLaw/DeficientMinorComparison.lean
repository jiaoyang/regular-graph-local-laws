import LocalLaw.ScalarMinorStability
import LocalLaw.MinorPivotRatios
import LocalLaw.BoundaryPivot
import LocalLaw.BoundarySchurRows

/-!
# Singleton comparison without a cap on the full reference inverse

A genuine deleted-model kernel bound supplies the two full pivot ratios and
the reciprocal pivot. The actual physical minor comparison then uses only
four full-entry approximation errors, with all pivot obligations derived.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance deficientMinorDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

theorem extensionMatrix_apply_of_ne (g : DeficientGraph V d) (q z : ℂ) (i j : V) (hij : i ≠ j) :
    g.extensionMatrix q z i j = g.H i j := by
  simp [extensionMatrix, boundaryMatrix, spectralMatrix, boundaryDiagonal,
    Matrix.diagonal_apply, Matrix.one_apply, hij]

theorem extensionMatrix_deleted_coupling_bounds (g : DeficientGraph V d) (hd : 3 ≤ d)
    (q z : ℂ) (b : V) :
    (∑ k : {k : V // k ≠ b}, ‖g.extensionMatrix q z b k.val‖) ≤ (d : ℝ) ∧
    (∑ k : {k : V // k ≠ b}, ‖g.extensionMatrix q z k.val b‖) ≤ (d : ℝ) := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hsqrt : 1 ≤ Real.sqrt ((d : ℝ) - 1) := by
    have hh := Real.sq_sqrt (show 0 ≤ (d : ℝ) - 1 by linarith)
    nlinarith [Real.sqrt_nonneg ((d : ℝ) - 1)]
  have hrow : (∑ k : {k : V // k ≠ b}, ‖g.extensionMatrix q z b k.val‖) ≤ (d : ℝ) := by
    have hsum := sum_deleted_add_at b (fun k : V => ‖g.H b k‖)
    have hdiag : g.H b b = 0 := normalizedAdjacency_zero_diagonal g.graph d b
    rw [hdiag, norm_zero, add_zero] at hsum
    calc
      _ = ∑ k : {k : V // k ≠ b}, ‖g.H b k.val‖ := by
        exact Finset.sum_congr rfl (fun k _ => congrArg norm (g.extensionMatrix_apply_of_ne q z b k.val k.property.symm))
      _ = ∑ k : V, ‖g.H b k‖ := hsum
      _ = (g.graph.degree b : ℝ) / Real.sqrt ((d : ℝ) - 1) := normalizedAdjacency_row_sum g.graph d b
      _ ≤ (d : ℝ) / Real.sqrt ((d : ℝ) - 1) :=
        div_le_div_of_nonneg_right (Nat.cast_le.mpr (g.degree_le b)) (Real.sqrt_nonneg _)
      _ ≤ d := (div_le_iff₀ (by linarith : 0 < Real.sqrt ((d : ℝ) - 1))).mpr (by nlinarith [show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg _])
  refine ⟨hrow, ?_⟩
  convert hrow using 1
  apply Finset.sum_congr rfl
  intro k _
  rw [g.extensionMatrix_apply_of_ne q z k.val b k.property,
    g.extensionMatrix_apply_of_ne q z b k.val k.property.symm]
  simp only [H, normalizedAdjacency_norm, g.graph.adj_comm]

def singletonPivotBudget (d : ℕ) (q z : ℂ) (C : ℝ) : ℝ :=
  (d : ℝ) + ‖z‖ + 2 * ‖q‖ + (d : ℝ) ^ 2 * C

/-- The actual deleted inverse controls the two reference pivot ratios and
the reciprocal pivot, even when the full inverse has large entries. -/
theorem singleton_pivot_ratio_bounds (g : DeficientGraph V d) (hd : 3 ≤ d)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (b : V) (C : ℝ) (hC : 0 ≤ C)
    (hkernel : ∀ i k : {i : V // i ≠ b},
      ‖((g.extensionMatrix q z).submatrix (Subtype.val : {i : V // i ≠ b} → V)
        (Subtype.val : {i : V // i ≠ b} → V))⁻¹ i k‖ ≤ C) :
    (∀ i : {i : V // i ≠ b}, ‖g.extensionGreen q z i.val b / g.extensionGreen q z b b‖ ≤ C * (d : ℝ)) ∧
    (∀ i : {i : V // i ≠ b}, ‖g.extensionGreen q z b i.val / g.extensionGreen q z b b‖ ≤ C * (d : ℝ)) ∧
    ‖(g.extensionGreen q z b b)⁻¹‖ ≤ singletonPivotBudget d q z C := by
  let A := g.extensionMatrix q z
  let P := g.extensionGreen q z
  have hunit := g.extensionMatrix_isUnit hd q z hz hq
  have hleft : P * A = 1 := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hunit)
  have hright : A * P = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hunit)
  have hpivot := g.extensionGreen_diagonal_ne_zero hd q z hz hq b
  have hcoupling := g.extensionMatrix_deleted_coupling_bounds hd q z b
  have hratio (i : {i : V // i ≠ b}) : ‖P i.val b / P b b‖ ≤ C * (d : ℝ) :=
    inverse_deleted_column_ratio_bound A P b hleft hpivot C d hC hkernel hcoupling.2 i
  have hdiag : ‖A b b‖ ≤ (d : ℝ) + ‖z‖ + 2 * ‖q‖ := by
    have hsum := g.extensionMatrix_row_sum_bound hd q z b
    have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
    have hsqrt : 1 ≤ Real.sqrt ((d : ℝ) - 1) := by
      have hh := Real.sq_sqrt (show 0 ≤ (d : ℝ) - 1 by linarith)
      nlinarith [Real.sqrt_nonneg ((d : ℝ) - 1)]
    have hnorm : ‖A b b‖ ≤ ∑ k : V, ‖g.extensionMatrix q z b k‖ :=
      Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ b)
    have hfrac : (d : ℝ) / Real.sqrt ((d : ℝ) - 1) ≤ d :=
      (div_le_iff₀ (by linarith : 0 < Real.sqrt ((d : ℝ) - 1))).mpr (by nlinarith [show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg _])
    linarith
  refine ⟨hratio, ?_, ?_⟩
  · intro i
    rw [(g.extensionGreen_isSymm q z).apply i.val b]
    exact hratio i
  · have hh := inverse_pivot_norm_bound A P b hright hpivot
      ((d : ℝ) + ‖z‖ + 2 * ‖q‖) d (C * (d : ℝ)) (by positivity) hdiag hcoupling.1 hratio
    convert hh using 1
    dsimp [singletonPivotBudget]
    ring

/-- Actual singleton Schur comparison using only four full-entry errors and
a bound on the genuine deleted reference kernel. The ambient physical graph
and the finite model may have different vertex types and sizes. -/
theorem embedded_singleton_minor_comparison {W : Type*} [Fintype W] [DecidableEq W]
    (g : DeficientGraph V d) (hd : 3 ≤ d) (H : Matrix W W ℂ) (hH : H.IsHermitian) (e : V ↪ W)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (b : V) (i : {i : V // i ≠ b})
    (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hkernel : ∀ k l : {k : V // k ≠ b},
      ‖((g.extensionMatrix q z).submatrix (Subtype.val : {i : V // i ≠ b} → V)
        (Subtype.val : {i : V // i ≠ b} → V))⁻¹ k l‖ ≤ C)
    (hcc : ‖green H z (e i.val) (e i.val) - g.extensionGreen q z i.val i.val‖ ≤ δ)
    (hcb : ‖green H z (e i.val) (e b) - g.extensionGreen q z i.val b‖ ≤ δ)
    (hbc : ‖green H z (e b) (e i.val) - g.extensionGreen q z b i.val‖ ≤ δ)
    (hbb : ‖green H z (e b) (e b) - g.extensionGreen q z b b‖ ≤ δ)
    (small : singletonPivotBudget d q z C * δ ≤ 1 / 2) :
    ‖green (deletedMatrix H (e b)) z
        ⟨e i.val, fun hh => i.property (e.injective hh)⟩
        ⟨e i.val, fun hh => i.property (e.injective hh)⟩ -
      ((g.extensionMatrix q z).submatrix (Subtype.val : {i : V // i ≠ b} → V)
        (Subtype.val : {i : V // i ≠ b} → V))⁻¹ i i‖ ≤
          2 * (C * (d : ℝ) + 1) ^ 2 * δ := by
  have hratios := g.singleton_pivot_ratio_bounds hd q z hz hq b C hC hkernel
  have hpivot := g.extensionGreen_diagonal_ne_zero hd q z hz hq b
  have hunit := g.extensionMatrix_isUnit hd q z hz hq
  have hleft : g.extensionGreen q z * g.extensionMatrix q z = 1 :=
    Matrix.nonsing_inv_mul (g.extensionMatrix q z) ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  have hdeleted := deleted_matrix_inverse (g.extensionMatrix q z) (g.extensionGreen q z) b hleft hpivot
  have hmodel := congrFun (congrFun hdeleted i) i
  change ((g.extensionMatrix q z).submatrix
    (Subtype.val : {i : V // i ≠ b} → V) (Subtype.val : {i : V // i ≠ b} → V))⁻¹ i i =
      g.extensionGreen q z i.val i.val - g.extensionGreen q z i.val b *
        g.extensionGreen q z b i.val / g.extensionGreen q z b b at hmodel
  let ii : {w : W // w ≠ e b} := ⟨e i.val, fun hh => i.property (e.injective hh)⟩
  have hphysical := green_deleted_vertex H hH z hz (e b) ii ii
  have hbound := scalar_minor_stability_from_ratios
    (green H z (e i.val) (e i.val)) (green H z (e i.val) (e b))
    (green H z (e b) (e i.val)) (green H z (e b) (e b))
    (g.extensionGreen q z i.val i.val) (g.extensionGreen q z i.val b)
    (g.extensionGreen q z b i.val) (g.extensionGreen q z b b)
    (C * (d : ℝ)) (singletonPivotBudget d q z C) δ hpivot (by positivity) hδ
    hratios.2.2 (hratios.1 i) (hratios.2.1 i) hcc hcb hbc hbb small
  rw [← hphysical, ← hmodel] at hbound
  exact hbound

end DeficientGraph
end LocalLaw
