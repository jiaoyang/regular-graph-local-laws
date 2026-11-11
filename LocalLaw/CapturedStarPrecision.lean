import LocalLaw.GraphPowerLocality
import LocalLaw.DeficientGraphModel

/-! # Captured sampled stars have literally identical precision rows

An induced restriction preserves the full degree at a vertex whose entire
neighbor set is captured. It consequently preserves the diagonal boundary
coefficient as well as every off-diagonal precision entry in that row.
-/

noncomputable section
namespace LocalLaw
local instance capturedStarPrecisionDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V:Type} [Fintype V] [DecidableEq V] {d:ℕ}

theorem extensionMatrix_isSymm (g:DeficientGraph V d)(q z:ℂ) :
    (g.extensionMatrix q z).IsSymm := by
  have hH:g.H.transpose=g.H:=by
    ext i j
    simp [H,normalizedAdjacency,SimpleGraph.adjMatrix_apply,g.graph.adj_comm]
  change (g.extensionMatrix q z).transpose=g.extensionMatrix q z
  simp only [extensionMatrix,boundaryMatrix,spectralMatrix,boundaryDiagonal,
    Matrix.transpose_sub,Matrix.transpose_smul,Matrix.transpose_one,Matrix.diagonal_transpose,hH]

theorem restrict_extensionMatrix_captured_row (g:DeficientGraph V d)(S:Set V)(v:S)
    (hcap:∀w,g.graph.Adj v.val w→w∈S)(q z:ℂ)(w:S) :
    (g.restrict S).extensionMatrix q z v w=g.extensionMatrix q z v.val w.val := by
  have hd:(g.restrict S).graph.degree v=g.graph.degree v.val:=
    induced_degree_eq_of_neighbors_inside g.graph S v hcap
  have hc:(g.restrict S).boundaryCoefficient v=g.boundaryCoefficient v.val:=by
    unfold boundaryCoefficient
    rw [hd]
    rfl
  have hH:(g.restrict S).H=g.H.submatrix (Subtype.val:S→V) (Subtype.val:S→V):=
    normalizedAdjacency_induce g.graph d S
  simp only [extensionMatrix,boundaryMatrix,spectralMatrix,boundaryDiagonal,
    Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Matrix.diagonal_apply]
  rw [hH]
  simp only [Matrix.submatrix_apply,Subtype.val_injective.eq_iff,hc]

theorem restrict_extensionMatrix_captured_column (g:DeficientGraph V d)(S:Set V)(v:S)
    (hcap:∀w,g.graph.Adj v.val w→w∈S)(q z:ℂ)(w:S) :
    (g.restrict S).extensionMatrix q z w v=g.extensionMatrix q z w.val v.val := by
  rw [((g.restrict S).extensionMatrix_isSymm q z).apply v w,
    (g.extensionMatrix_isSymm q z).apply v.val w.val]
  exact g.restrict_extensionMatrix_captured_row S v hcap q z w

end DeficientGraph
end LocalLaw
