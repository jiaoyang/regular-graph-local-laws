import LocalLaw.OptionalRetainedEdges

/-! # Genuine edge-erased core inverse for the full switching benchmark -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance optionalEdgeCutPrecisionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 2000000
variable {V K I : Type} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I] in
theorem optionalRetainedGraph_map_le (G : SimpleGraph V) (e : K ↪ V)
    (inner outer : I → Option K)
    (hedges : ∀ i x y, inner i = some x → outer i = some y → G.Adj (e x) (e y)) :
    (optionalRetainedGraph inner outer).map e ≤ G := by
  rintro _ _ ⟨x,y,hxy,rfl,rfl⟩
  obtain ⟨i,hi⟩ := hxy.2
  rcases hi with hi | hi
  · exact hedges i x y hi.1 hi.2
  · exact (hedges i y x hi.2 hi.1).symm

namespace DeficientGraph
variable {d : ℕ}

def optionalEdgeCut (g : DeficientGraph V d) (e : K ↪ V) (inner outer : I → Option K) :
    DeficientGraph V d :=
  g.edgeSubgraph (g.graph \ (optionalRetainedGraph inner outer).map e) sdiff_le

omit [DecidableEq V] [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I] in
theorem optionalEdgeCut_reference_budget (g : DeficientGraph V d) (e : K ↪ V)
    (inner outer : I → Option K) (hb : g.ComponentFiniteReferenceBudget) :
    (g.optionalEdgeCut e inner outer).ComponentFiniteReferenceBudget :=
  g.edgeSubgraph_componentFiniteReferenceBudget _ sdiff_le hb

theorem optionalEdgeCut_retained_inverse (g : DeficientGraph V d) (hd : 3 ≤ d)
    (e : K ↪ V) (inner outer : I → Option K)
    (houter : ∀ i j k, outer i = some k → outer j = some k → i = j)
    (hdisjoint : ∀ i j k, inner i = some k → outer j ≠ some k)
    (hedges : ∀ i x y, inner i = some x → outer i = some y → g.graph.Adj (e x) (e y))
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let P := (g.extensionGreen q z).submatrix e e
    let A := P⁻¹ - fullQuadRetainedEdges inner outer (treeEdgeWeight d) -
      Matrix.diagonal (fun k => q * treeEdgeWeight d ^ 2 * fullQuadRetainedDegree inner outer k)
    IsUnit A ∧ A⁻¹ = ((g.optionalEdgeCut e inner outer).extensionGreen q z).submatrix e e := by
  dsimp only
  let R := optionalRetainedGraph inner outer
  let cut := g.optionalEdgeCut e inner outer
  let E := fullQuadRetainedEdges inner outer (treeEdgeWeight d)
  let P := (g.extensionGreen q z).submatrix e e
  let Q := (cut.extensionGreen q z).submatrix e e
  have hR : R.map e ≤ g.graph := optionalRetainedGraph_map_le g.graph e inner outer hedges
  have hδ : ∀ v, cut.deficit v = g.deficit v := fun _ => rfl
  have hDelta (x y : V) : (cut.H - g.H) x y = -normalizedAdjacency (R.map e) d x y := by
    change normalizedAdjacency (g.graph \ R.map e) d x y - normalizedAdjacency g.graph d x y = _
    by_cases hr : (R.map e).Adj x y
    · have hg := hR hr
      simp only [normalizedAdjacency,Matrix.smul_apply,smul_eq_mul,SimpleGraph.adjMatrix_apply,
        SimpleGraph.sdiff_adj,hr,hg,not_true_eq_false,and_false,if_false,if_true,mul_zero,mul_one,zero_sub]
    · simp only [normalizedAdjacency,Matrix.smul_apply,smul_eq_mul,SimpleGraph.adjMatrix_apply,
        SimpleGraph.sdiff_adj,hr,not_false_eq_true,and_true,if_false,mul_zero,neg_zero,sub_self]
  have hsupport : ∀ x y, x ∉ Set.range e ∨ y ∉ Set.range e → (cut.H-g.H) x y = 0 := by
    intro x y hxy
    have hr : ¬(R.map e).Adj x y := by
      rintro ⟨u,v,_,hu,hv⟩
      exact hxy.elim (fun h => h ⟨u,hu⟩) (fun h => h ⟨v,hv⟩)
    rw [hDelta]
    simp only [normalizedAdjacency,Matrix.smul_apply,smul_eq_mul,SimpleGraph.adjMatrix_apply,
      hr,if_false,mul_zero,neg_zero]
  have hE : (cut.H-g.H).submatrix e e = -E := by
    ext x y
    rw [Matrix.submatrix_apply,hDelta]
    change -normalizedAdjacency (R.map e) d (e x) (e y) = -E x y
    have hm : normalizedAdjacency (R.map e) d (e x) (e y) = normalizedAdjacency R d x y := by
      simp only [normalizedAdjacency,Matrix.smul_apply,smul_eq_mul,SimpleGraph.adjMatrix_apply,
        SimpleGraph.map_adj_apply]
    rw [hm]
    have he := optionalRetainedGraph_normalizedAdjacency inner outer houter hdisjoint d
    exact congrArg Neg.neg (congrArg (fun M : Matrix K K ℂ => M x y) he)
  have hh := g.supported_retained_inverse cut hd e q z hz hq
    (g.extensionMatrix_difference_supported_of_H cut hd hδ e hsupport q z)
  have hc := g.supported_extensionMatrix_difference_row_charge cut hd hδ e hsupport q z
  have hentry (x y : K) : (cut.H - g.H) (e x) (e y) = -E x y :=
    congrArg (fun M : Matrix K K ℂ => M x y) hE
  have hInv : Q⁻¹ = P⁻¹ - E -
      Matrix.diagonal (fun k => q * treeEdgeWeight d ^ 2 * fullQuadRetainedDegree inner outer k) := by
    rw [hh.2.2,hc,hE]
    simp_rw [hentry]
    ext x y
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.neg_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.diagonal_apply,Finset.sum_neg_distrib]
    have hrow := fullQuadRetainedEdges_row inner outer (treeEdgeWeight d) x
    change (∑ j,E x j) = _ at hrow
    rw [hrow]
    dsimp only [P]
    by_cases hxy : x = y
    · subst y
      simp only [if_true]
      ring
    · simp only [hxy,if_false,mul_zero,sub_zero,add_zero]
      ring
  have hQ : IsUnit Q := hh.2.1
  have hQinv : IsUnit Q⁻¹ := Matrix.isUnit_of_right_inverse
    (Matrix.nonsing_inv_mul Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ))
  refine ⟨hInv ▸ hQinv,?_⟩
  rw [←hInv]
  exact Matrix.nonsing_inv_nonsing_inv Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ)

end DeficientGraph
end LocalLaw
