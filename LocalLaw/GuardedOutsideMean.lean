import LocalLaw.GuardedCavityAverage
import LocalLaw.BoundarySupportedDeletion
import LocalLaw.OutsideCavityMean
import LocalLaw.SourceBoundaryGuard

/-!
# The far-boundary one-edge mean from local physical caps

The principal-deletion Ward cost, removed oriented edges, and rejected far
mask are counted separately. Deleted pivot bounds are used only on the guard.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance guardedOutsideMeanDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

def outsideMatrixCavityValue (G : SimpleGraph V) (T : Set V)
    (R : Matrix V V ℂ) (e : OutsideOrientedEdge G T) : ℂ := matrixCavityTerm R e.val.2 e.val.1

omit [DecidableEq V] in
theorem outsideMatrixCavityValue_sum (G : SimpleGraph V) (T : Set V) (R : Matrix V V ℂ) :
    (∑ e : OutsideOrientedEdge G T, outsideMatrixCavityValue G T R e) =
      ∑ i, ∑ j, if (outsideSpanningGraph G T).Adj i j then
        matrixCavityTerm (R) i j else 0 := by
  let f : V × V → ℂ := fun p =>
    matrixCavityTerm (R) p.2 p.1
  have he : ∀ e : OutsideOrientedEdge G T, outsideMatrixCavityValue G T R e = f e.val := by
    intro e
    rfl
  rw [Finset.sum_congr rfl (fun e _ => he e)]
  have hs : (∑ p ∈ Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∉ T ∧ p.2 ∉ T), f p) =
      ∑ e : OutsideOrientedEdge G T, f e.val := by
    exact Finset.sum_subtype _ (by simp) _
  rw [← hs, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [f, outsideSpanningGraph]
  congr 1
  exact propext (by rw [G.adj_comm]; tauto)

omit [Fintype V] [DecidableEq V] in
theorem outsideMatrixCavityValue_norm_bound (G : SimpleGraph V) (T : Set V)
    (R : Matrix V V ℂ) (C L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hRd : ∀ i, ‖R i i‖ ≤ C) (hRe : ∀ i j, G.Adj i j → ‖R i j‖ ≤ C)
    (hRi : ∀ i, ‖(R i i)⁻¹‖ ≤ L) (e : OutsideOrientedEdge G T) :
    ‖outsideMatrixCavityValue G T R e‖ ≤ C + C ^ 2 * L := by
  rw [outsideMatrixCavityValue, ← matrixCavityTerm_edgeLocal G R e.property.1.symm]
  exact matrixCavityTerm_norm_bound _ C L hC hL
    (edgeLocalMatrix_norm_bound G R C hC hRd hRe)
    (by intro i; simpa only [edgeLocalMatrix_diagonal] using hRi i) _ _

/-- The finite mean lost by a mask is bounded by its actual rejected count. -/
theorem finiteComplexMean_mask_difference {E : Type*} [Fintype E]
    (p : E → Prop) (f : E → ℂ) (M : ℝ) (_hM : 0 ≤ M) (hf : ∀ e, ‖f e‖ ≤ M) :
    ‖finiteComplexMean f - finiteComplexMean (fun e => if p e then f e else 0)‖ ≤
      (Fintype.card E : ℝ)⁻¹ * (Nat.card {e : E // ¬p e} : ℝ) * M := by
  unfold finiteComplexMean
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← Finset.sum_sub_distrib]
  have hp : ∀ e, ‖f e - (if p e then f e else 0)‖ ≤ (if ¬p e then M else 0) := by
    intro e
    by_cases he : p e
    · simp [he]
    · simpa only [he, if_false, not_false_eq_true, if_true, sub_zero] using hf e
  have hs : (∑ e : E, if ¬p e then M else 0) = (Nat.card {e : E // ¬p e} : ℝ) * M := by
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc
    _ ≤ (Fintype.card E : ℝ)⁻¹ * (∑ e : E, if ¬p e then M else 0) :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ => hp e))) (by positivity)
    _ = _ := by rw [hs]; ring

namespace RegularGraph
variable {N d : ℕ}

/-- Actual Q versus the outside guarded cavity sum; the omitted-edge cost
uses only the physical regular graph and local cavity caps. -/
theorem Q_outside_guarded_cavity_average_difference (g : RegularGraph N d) (T A : Set (Fin N))
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
      (∑ e : OutsideOrientedEdge g.graph T,
        outsideMatrixCavityValue g.graph T (guardedDeletedGreen g.H T A z) e)‖ ≤
      ((N : ℝ) * (d : ℝ))⁻¹ *
        ((((d : ℝ) * (1 + C * L) ^ 2 * I / z.im) *
          (∑ u : T, ∑ v : T,
            ‖((g.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N))⁻¹ u v‖)) +
            (2 * (d : ℝ) * (Nat.card T : ℝ)) * (C + C ^ 2 * L)) := by
  let R := edgeLocalMatrix g.graph (g.G z)
  let S := edgeLocalMatrix g.graph (guardedDeletedGreen g.H T A z)
  have hsum := edge_cavity_sums_difference g.graph (outsideSpanningGraph g.graph T)
    R S (C + C ^ 2 * L)
    (matrixCavityTerm_norm_bound R C L hC hL
      (edgeLocalMatrix_norm_bound g.graph (g.G z) C hC hRd hRe)
      (by intro i; simpa only [R, edgeLocalMatrix_diagonal] using hRi i))
    (matrixCavityTerm_norm_bound S C L hC hL
      (edgeLocalMatrix_norm_bound g.graph (guardedDeletedGreen g.H T A z) C hC hSd hSe)
      (by intro i; simpa only [S, edgeLocalMatrix_diagonal] using hSi i))
  have hterm : ∀ i j, (if g.graph.Adj i j then
      ‖matrixCavityTerm R i j - matrixCavityTerm S i j‖ else 0) =
      (if g.graph.Adj i j then ‖matrixCavityTerm (g.G z) i j -
        matrixCavityTerm (guardedDeletedGreen g.H T A z) i j‖ else 0) := by
    intro i j
    by_cases hij : g.graph.Adj i j <;> simp only [hij, if_true, if_false]
    simp only [R, S, matrixCavityTerm_edgeLocal g.graph _ hij]
  have hleft : (∑ i, ∑ j, if g.graph.Adj i j then matrixCavityTerm R i j else 0) =
      ∑ i, ∑ j, if g.graph.Adj i j then matrixCavityTerm (g.G z) i j else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : g.graph.Adj i j <;> simp only [hij, if_true, if_false]
    exact matrixCavityTerm_edgeLocal g.graph _ hij
  have hright : (∑ i, ∑ j, if (outsideSpanningGraph g.graph T).Adj i j then matrixCavityTerm S i j else 0) =
      ∑ e : OutsideOrientedEdge g.graph T,
        outsideMatrixCavityValue g.graph T (guardedDeletedGreen g.H T A z) e := by
    rw [outsideMatrixCavityValue_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : (outsideSpanningGraph g.graph T).Adj i j <;> simp only [hij, if_true, if_false]
    exact matrixCavityTerm_edgeLocal g.graph _ hij.1
  simp_rw [hterm] at hsum
  rw [hleft, hright] at hsum
  have hward := regular_edge_guardedDeletion_difference_ward g.graph d g.regular g.H
    (normalizedAdjacency_isHermitian g.graph d) T A z hz C L I hC hL
    hRd hRe hRi hSd hSe hSp hSi hI
  have hcount := outsideSpanningGraph_disagreement g.graph d g.regular T
  have hbound := hsum.trans (add_le_add hward
    (mul_le_mul_of_nonneg_right hcount (by positivity : 0 ≤ C + C ^ 2 * L)))
  change ‖cavityAverage g.graph d z - _‖ ≤ _
  rw [cavityAverage_eq_matrixCavityTerm g.graph d z hz]
  simp only [Fintype.card_fin, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_natCast, ← mul_sub, norm_mul, norm_inv, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

end RegularGraph
end LocalLaw
