import LocalLaw.CavityDeletionAverage
import LocalLaw.BoundarySchurRows
import LocalLaw.DeletionStability

/-!
# A concrete inverse-block bound for physical deletion averages

A uniform bound on the actual outside Green matrix controls the retained
inverse block through its exact Schur formula. The resulting quadratic removed
set cost has the same logarithmic order used in the source bias estimate.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance cavityDeleteBoundsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def deletionInverseEntryCap (d : ℕ) (B C : ℝ) : ℝ :=
  B + (Real.sqrt ((d : ℝ) - 1))⁻¹ + ((d : ℝ) / Real.sqrt ((d : ℝ) - 1)) ^ 2 * C

namespace RegularGraph
variable {N d : ℕ}

theorem physical_retained_inverse_entry_bound (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (hz : 0 < z.im) (B C : ℝ) (hzB : ‖z‖ ≤ B) (hC : 0 ≤ C)
    (hS : ∀ i j : (Tᶜ : Set (Fin N)),
      ‖green (normalizedAdjacency (outsideGraph g.graph T) d) z i j‖ ≤ C) (i j : T) :
    ‖((g.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N))⁻¹ i j‖ ≤
      deletionInverseEntryCap d B C := by
  let A := g.H.submatrix (Subtype.val : T → Fin N) (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)
  let S := green (g.H.submatrix (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)
    (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)) z
  let B' := g.H.submatrix (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N) (Subtype.val : T → Fin N)
  let w := (d : ℝ) / Real.sqrt ((d : ℝ) - 1)
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hrow : ∑ a, ‖A i a‖ ≤ w :=
    normalized_cut_left_row_bound g.graph d T (fun v => (g.regular v).le) i
  have hcol : ∑ a, ‖B' a j‖ ≤ w := by
    have hh := normalized_cut_left_row_bound g.graph d T (fun v => (g.regular v).le) j
    simpa only [A, B', Matrix.submatrix_apply, RegularGraph.H, normalizedAdjacency_norm,
      g.graph.adj_comm] using hh
  have hAS : ∀ a, ‖(A * S) i a‖ ≤ w * C := by
    intro a
    exact rectangular_product_row_bound A S i a w C hC hrow (fun b => hS b a)
  have henergy : ‖(A * S * B') i j‖ ≤ (w * C) * w :=
    rectangular_product_column_bound (A * S) B' i j (w * C) w (mul_nonneg hw hC) hAS hcol
  have hHentry : ‖g.H i.val j.val‖ ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹ := by
    simp only [RegularGraph.H, normalizedAdjacency_norm]
    split_ifs
    · exact le_rfl
    · exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hshift : ‖spectralMatrix
      (g.H.submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N)) z i j‖ ≤
      B + (Real.sqrt ((d : ℝ) - 1))⁻¹ := by
    have hh := norm_sub_le (g.H i.val j.val) ((z • (1 : Matrix T T ℂ)) i j)
    have hdiag : ‖(z • (1 : Matrix T T ℂ)) i j‖ ≤ ‖z‖ := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    exact hh.trans (by linarith)
  have hid := congrArg (fun M : Matrix T T ℂ => M i j)
    (green_retained_principal_inverse T g.H (normalizedAdjacency_isHermitian g.graph d) z hz).2
  change ((g.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N))⁻¹ i j =
    spectralMatrix (g.H.submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N)) z i j -
      (A * S * B') i j at hid
  rw [hid]
  apply (norm_sub_le _ _).trans
  apply (add_le_add hshift henergy).trans_eq
  dsimp only [deletionInverseEntryCap, w]
  ring

theorem physical_retained_inverse_mass_bound (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (hz : 0 < z.im) (B C : ℝ) (hzB : ‖z‖ ≤ B) (hC : 0 ≤ C)
    (hS : ∀ i j : (Tᶜ : Set (Fin N)),
      ‖green (normalizedAdjacency (outsideGraph g.graph T) d) z i j‖ ≤ C) :
    (∑ i : T, ∑ j : T,
      ‖((g.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N))⁻¹ i j‖) ≤
      (Nat.card T : ℝ) ^ 2 * deletionInverseEntryCap d B C := by
  calc
    _ ≤ ∑ _i : T, ∑ _j : T, deletionInverseEntryCap d B C :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        g.physical_retained_inverse_entry_bound T z hz B C hzB hC hS i j))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card]; ring

end RegularGraph
end
end LocalLaw
