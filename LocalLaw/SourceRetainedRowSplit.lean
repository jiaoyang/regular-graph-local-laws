import LocalLaw.SourceRetainedExactRow
import LocalLaw.SourceRetainedProductWeights
import LocalLaw.SourceRetainedWeights

/-! # Exact diagonal/off-diagonal split on the original boundary labels -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceRetainedRowSplitDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem weighted_double_sum_diagonal_split {I : Type*} [Fintype I]
    (A B : I → ℂ) (D : Matrix I I ℂ) :
    (∑ i, ∑ j, A i * D i j * B j) =
      (∑ i, A i * B i * D i i) + ∑ i, ∑ j, if i = j then 0 else A i * D i j * B j := by
  have hrow (i : I) : (∑ j, A i * D i j * B j) = A i * B i * D i i +
      ∑ j, if i = j then 0 else A i * D i j * B j := by
    calc
      _ = ∑ j, ((if i = j then A i * D i j * B j else 0) +
          (if i = j then 0 else A i * D i j * B j)) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring
  calc
    _ = ∑ i, (A i * B i * D i i + ∑ j, if i = j then 0 else A i * D i j * B j) :=
      Finset.sum_congr rfl (fun i _ => hrow i)
    _ = _ := Finset.sum_add_distrib

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

/-- The physical row difference is controlled by the three actual forcing
terms, with the squared edge normalization bounded by one. -/
theorem sourceRetained_row_norm_split (g : RegularGraph N d) (hd : 3 ≤ d)
    (o : Fin N) (ell selector r : ℕ) (hsep : 2*r+2≤selector) (hr : r+2≤selector)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (y : graphBallVertices g.graph o ell) :
    let T := graphBallVertices g.graph o ell
    let root : T := ⟨o,center_mem_graphBall g.graph o ell⟩
    let gnew := g.labelledResampledGraph T labels samples selector
    let R := (gnew.G z).submatrix (Subtype.val:T→Fin N) (Subtype.val:T→Fin N)
    let P := g.sourceRetainedReference T r q z
    let U := g.sourceCutCoupling T labels
    let D := g.sourceBoundaryDefect T labels samples selector r q z
    let l := fun i => cutInsideVertex g.graph T (labels i)
    ‖gnew.G z o y.val-P root y‖ ≤
      ‖∑ i,g.sourceRetainedProductWeights o ell r q z y (labels i)*D i i‖ +
      ‖∑ i,∑ j,if i=j then 0 else P root (l i)*D i j*P (l j) y‖ +
      ‖((R-P)*U*D*U.transpose*P) root y‖ := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let root : T := ⟨o,center_mem_graphBall g.graph o ell⟩
  let gnew := g.labelledResampledGraph T labels samples selector
  let R := (gnew.G z).submatrix (Subtype.val:T→Fin N) (Subtype.val:T→Fin N)
  let P := g.sourceRetainedReference T r q z
  let U := g.sourceCutCoupling T labels
  let D := g.sourceBoundaryDefect T labels samples selector r q z
  let l := fun i => cutInsideVertex g.graph T (labels i)
  let c : ℂ := (↑((Real.sqrt ((d:ℝ)-1))⁻¹):ℂ)^2
  have hrow := g.sourceRetained_exact_row hd T labels samples selector r hsep hr q z hz hq root y
  dsimp only at hrow
  have hsym : P.IsSymm := g.sourceRetainedReference_isSymm T r q z
  have hdiag : (∑ i,P root (l i)*P (l i) y*D i i) =
      ∑ i,g.sourceRetainedProductWeights o ell r q z y (labels i)*D i i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hsym.apply y (l i)]
    rfl
  have hsplit := weighted_double_sum_diagonal_split (fun i=>P root (l i)) (fun i=>P (l i) y) D
  have hrem := g.sourceRetained_remainder_formula T labels R P D root y
  have heq : R root y-P root y =
      (c*(∑ i,g.sourceRetainedProductWeights o ell r q z y (labels i)*D i i)+
        c*(∑ i,∑ j,if i=j then 0 else P root (l i)*D i j*P (l j) y)) +
        ((R-P)*U*D*U.transpose*P) root y := by
    rw [hrow, hsplit, hdiag, mul_add, hrem]
  rw [show gnew.G z o y.val-P root y=R root y-P root y from rfl, heq]
  apply ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)).trans
  have hc := cut_coefficient_norm_le_one d hd
  apply add_le_add_right
  apply add_le_add
  · rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hc
  · rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hc

end RegularGraph
end LocalLaw
