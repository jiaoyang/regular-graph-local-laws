import LocalLaw.DeficientGraphModel

/-!
# Isomorphism covariance of actual deficient finite models

Both the normalized adjacency and the missing-degree boundary coefficient
are transported through an actual graph isomorphism with matching deficits.
The genuine matrix inverse then reindexes by finite equivalence.
-/

noncomputable section
namespace LocalLaw
local instance deficientIsoDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] {d : ℕ}

theorem extensionMatrix_iso (g : DeficientGraph V d) (h : DeficientGraph W d)
    (e : h.graph ≃g g.graph) (hdeficit : ∀ v, h.deficit v = g.deficit (e v)) (q z : ℂ) :
    (g.extensionMatrix q z).submatrix e e = h.extensionMatrix q z := by
  have hdegree (v : W) : h.graph.degree v = g.graph.degree (e v) := by
    have hh := Nat.card_congr (e.mapNeighborSet v)
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    exact hh
  ext i j
  simp only [extensionMatrix, boundaryMatrix, spectralMatrix, H, boundaryDiagonal,
    boundaryCoefficient, hdeficit, hdegree, Matrix.submatrix_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply, Matrix.one_apply,
    normalizedAdjacency, SimpleGraph.adjMatrix_apply]
  rw [show g.graph.Adj (e i) (e j) ↔ h.graph.Adj i j from e.map_rel_iff']
  simp only [e.injective.eq_iff]

theorem extensionGreen_iso (g : DeficientGraph V d) (h : DeficientGraph W d)
    (e : h.graph ≃g g.graph) (hdeficit : ∀ v, h.deficit v = g.deficit (e v)) (q z : ℂ) :
    (g.extensionGreen q z).submatrix e e = h.extensionGreen q z := by
  have hh := Matrix.inv_submatrix_equiv (g.extensionMatrix q z) e.toEquiv e.toEquiv
  change ((g.extensionMatrix q z).submatrix e e)⁻¹ = (g.extensionMatrix q z)⁻¹.submatrix e e at hh
  rw [g.extensionMatrix_iso h e hdeficit q z] at hh
  exact hh.symm

end DeficientGraph
end LocalLaw
