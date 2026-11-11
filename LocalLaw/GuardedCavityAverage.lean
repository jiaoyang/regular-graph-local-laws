import LocalLaw.EdgeLocalCavity
import LocalLaw.GuardedDeletionWard
import LocalLaw.CavityDeletionAverage

/-!
# Guarded physical deletion and the actual cavity average

Only diagonal and adjacent entries, and deleted pivots on a chosen safe set,
are needed. Weighted Ward controls the actual physical principal correction.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance guardedCavityAverageDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem regular_edge_guardedDeletion_difference_ward (G : SimpleGraph V) (d : ℕ)
    (hregular : G.IsRegularOfDegree d) (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (T A : Set V) (z : ℂ) (hz : 0 < z.im) (C L I : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hRd : ∀ i, ‖green H z i i‖ ≤ C)
    (hRe : ∀ i j, G.Adj i j → ‖green H z i j‖ ≤ C)
    (hRi : ∀ j, ‖(green H z j j)⁻¹‖ ≤ L)
    (hSd : ∀ i, ‖guardedDeletedGreen H T A z i i‖ ≤ C)
    (hSe : ∀ i j, G.Adj i j → ‖guardedDeletedGreen H T A z i j‖ ≤ C)
    (hSp : ∀ j, guardedDeletedGreen H T A z j j ≠ 0)
    (hSi : ∀ j, ‖(guardedDeletedGreen H T A z j j)⁻¹‖ ≤ L)
    (hI : ∀ u, (green H z u u).im ≤ I) :
    (∑ i, ∑ j, if G.Adj i j then
      ‖matrixCavityTerm (green H z) i j - matrixCavityTerm (guardedDeletedGreen H T A z) i j‖ else 0) ≤
      ((d : ℝ) * (1 + C * L) ^ 2 * I / z.im) *
        (∑ u : T, ∑ v : T,
          ‖((green H z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ u v‖) := by
  have hbase := regular_edge_cavity_difference_local G d hregular (green H z)
    (guardedDeletedGreen H T A z) C L hC hL hRd hRe hSd hSe
    (green_diagonal_ne_zero H hH z hz) hSp hRi hSi
  have hdiag : (∑ i, ‖green H z i i - guardedDeletedGreen H T A z i i‖) ≤
      (I / z.im) * (∑ u : T, ∑ v : T,
        ‖((green H z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ u v‖) := by
    simpa only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.sum_ite_eq, Finset.mem_univ, if_true] using
      weighted_guardedDeletedGreen_difference_ward H hH T A z hz (1 : Matrix V V ℝ) 1 I
        (by intro i j; simp only [Matrix.one_apply]; split_ifs <;> norm_num)
        (by norm_num) (by intro i; simp [Matrix.one_apply]) (by intro j; simp [Matrix.one_apply]) hI
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
  have hedge := weighted_guardedDeletedGreen_difference_ward H hH T A z hz W (d : ℝ) I
    (by intro i j; dsimp only [W]; split_ifs <;> norm_num) (Nat.cast_nonneg d) hrow hcol hI
  simp only [W, ite_mul, one_mul, zero_mul] at hedge
  apply hbase.trans
  calc
    _ ≤ ((d : ℝ) * (1 + C ^ 2 * L ^ 2)) *
        ((I / z.im) * (∑ u : T, ∑ v : T,
          ‖((green H z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ u v‖)) +
        2 * C * L * (((d : ℝ) * I / z.im) * (∑ u : T, ∑ v : T,
          ‖((green H z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ u v‖)) :=
      add_le_add (mul_le_mul_of_nonneg_left hdiag (by positivity))
        (mul_le_mul_of_nonneg_left hedge (by positivity))
    _ = _ := by ring

omit [DecidableEq V] in
/-- Same-graph summation needs no bound for nonadjacent cavity terms. -/
theorem same_graph_cavity_sums_difference (G : SimpleGraph V) (R S : Matrix V V ℂ) :
    ‖(∑ i, ∑ j, if G.Adj i j then matrixCavityTerm R i j else 0) -
      (∑ i, ∑ j, if G.Adj i j then matrixCavityTerm S i j else 0)‖ ≤
      ∑ i, ∑ j, if G.Adj i j then ‖matrixCavityTerm R i j - matrixCavityTerm S i j‖ else 0 := by
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : G.Adj i j <;> simp [hij]

namespace RegularGraph
variable {N d : ℕ}

/-- The actual Q average versus the guarded physical cavity sum. -/
theorem Q_guarded_cavity_average_difference (g : RegularGraph N d) (T A : Set (Fin N))
    (z : ℂ) (hz : 0 < z.im) (C L I : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hRd : ∀ i, ‖g.G z i i‖ ≤ C)
    (hRe : ∀ i j, g.graph.Adj i j → ‖g.G z i j‖ ≤ C)
    (hRi : ∀ j, ‖(g.G z j j)⁻¹‖ ≤ L)
    (hSd : ∀ i, ‖guardedDeletedGreen g.H T A z i i‖ ≤ C)
    (hSe : ∀ i j, g.graph.Adj i j → ‖guardedDeletedGreen g.H T A z i j‖ ≤ C)
    (hSp : ∀ j, guardedDeletedGreen g.H T A z j j ≠ 0)
    (hSi : ∀ j, ‖(guardedDeletedGreen g.H T A z j j)⁻¹‖ ≤ L)
    (hI : ∀ u, (g.G z u u).im ≤ I) :
    ‖g.Q z - ((N : ℝ) * (d : ℝ))⁻¹ •
      (∑ i, ∑ j, if g.graph.Adj i j then
        matrixCavityTerm (guardedDeletedGreen g.H T A z) i j else 0)‖ ≤
      ((N : ℝ) * (d : ℝ))⁻¹ *
        (((d : ℝ) * (1 + C * L) ^ 2 * I / z.im) *
          (∑ u : T, ∑ v : T,
            ‖((g.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N))⁻¹ u v‖)) := by
  have hsum := same_graph_cavity_sums_difference g.graph (g.G z) (guardedDeletedGreen g.H T A z)
  have hward := regular_edge_guardedDeletion_difference_ward g.graph d g.regular g.H
    (normalizedAdjacency_isHermitian g.graph d) T A z hz C L I hC hL
    hRd hRe hRi hSd hSe hSp hSi hI
  have hbound := hsum.trans hward
  change ‖cavityAverage g.graph d z - _‖ ≤ _
  rw [cavityAverage_eq_matrixCavityTerm g.graph d z hz]
  simp only [Fintype.card_fin, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_natCast, ← mul_sub, norm_mul, norm_inv, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

end RegularGraph
end LocalLaw
