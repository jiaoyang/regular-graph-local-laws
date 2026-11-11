import LocalLaw.BoundarySchurExpansion
import LocalLaw.DeletedNeighborhoodCover

/-!
# Literal source neighborhood Schur expansion

The larger neighborhood contains every incident edge of its retained root
ball. Its retained boundary charge therefore vanishes exactly. The physical
and local models share their retained adjacency block, and the exact row
expansion is driven solely by the difference of their genuine deleted
self-energies.
-/

noncomputable section
namespace LocalLaw
local instance sourceBoundarySchurDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Degree
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Inducing on a set containing every neighbor preserves the actual degree. -/
theorem induce_degree_eq_of_neighbors (G : SimpleGraph V) (S : Set V) (x : S)
    (hS : ∀ y, G.Adj x.val y → y ∈ S) : (G.induce S).degree x = G.degree x.val := by
  let e : (G.induce S).neighborSet x ≃ G.neighborSet x.val :=
    { toFun := fun y => ⟨y.val.val, y.property⟩
      invFun := fun y => ⟨⟨y.val, hS y.val y.property⟩, y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hh := Nat.card_congr e
  simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] using hh

end Degree

namespace RegularGraph
variable {N d : ℕ}

/-- Every actual retained vertex has zero local boundary charge. This is a
geometric consequence of the radius-r expansion, not a model hypothesis. -/
theorem deletionNeighborhood_retained_boundary_zero (g : RegularGraph N d)
    (o i j : Fin N) (ell r : ℕ) (hr : 1 ≤ r)
    (x : deletionNeighborhoodInnerSet g.graph o i j ell r) :
    (g.deletionNeighborhoodModel o i j ell r).boundaryCoefficient x.val = 0 := by
  have hx : x.val.val ∈ graphBallVertices g.graph o ell :=
    (deletionNeighborhood_inner_mem g.graph o i j ell r x.val).mp x.property
  have hdegree := induce_degree_eq_of_neighbors g.graph (deletionNeighborhoodVertices g.graph o i j ell r)
    x.val (fun y hxy => deletionNeighborhood_contains_schur_ball g.graph o i j x.val.val ell r
      (Or.inl hx) ((SimpleGraph.edist_le (SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil)).trans
        (by simpa using (ENat.coe_le_coe.mpr hr))))
  have hdeg : (g.deletionNeighborhoodModel o i j ell r).graph.degree x.val = d :=
    hdegree.trans (g.regular x.val.val)
  unfold DeficientGraph.boundaryCoefficient
  rw [g.deletionNeighborhoodModel_zero_deficit, hdeg]
  simp

/-- The retained diagonal boundary matrix is literally zero. -/
theorem deletionNeighborhood_retained_boundaryDiagonal_zero (g : RegularGraph N d)
    (o i j : Fin N) (ell r : ℕ) (hr : 1 ≤ r) :
    ((g.deletionNeighborhoodModel o i j ell r).boundaryDiagonal).submatrix
      (Subtype.val : deletionNeighborhoodInnerSet g.graph o i j ell r → _)
      (Subtype.val : deletionNeighborhoodInnerSet g.graph o i j ell r → _) = 0 := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [DeficientGraph.boundaryDiagonal, Matrix.submatrix_apply, Matrix.diagonal_apply_eq,
      g.deletionNeighborhood_retained_boundary_zero o i j ell r hr, Complex.ofReal_zero, Matrix.zero_apply]
  · have hval : x.val ≠ y.val := fun hh => hxy (Subtype.ext hh)
    simp [DeficientGraph.boundaryDiagonal, hval]

/-- Source (5.85) on the actual finite neighborhood, with all physical inverse
units and shared retained adjacency derived. It applies in particular to the
actual fully resampled regular graph. -/
theorem deletionNeighborhood_retained_expansion (g : RegularGraph N d) (hd : 3 ≤ d)
    (o i j : Fin N) (ell r : ℕ) (hr : 1 ≤ r) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let M := g.deletionNeighborhoodModel o i j ell r
    let T := deletionNeighborhoodInnerSet g.graph o i j ell r
    let e : deletionNeighborhoodVertices g.graph o i j ell r ↪ Fin N := Function.Embedding.subtype _
    let R := ((g.G z).submatrix e e).submatrix (Subtype.val : T → _) (Subtype.val : T → _)
    let P := (M.extensionGreen q z).submatrix (Subtype.val : T → _) (Subtype.val : T → _)
    let W := embeddedSelfEnergy g.H e T z - M.retainedSelfEnergy T q z
    R - P = P * W * P + (R - P) * W * P := by
  dsimp only
  let M := g.deletionNeighborhoodModel o i j ell r
  let T := deletionNeighborhoodInnerSet g.graph o i j ell r
  let e : deletionNeighborhoodVertices g.graph o i j ell r ↪ Fin N := Function.Embedding.subtype _
  have hH : M.H = g.H.submatrix e e := normalizedAdjacency_induce g.graph d _
  have hh := M.embedded_retained_expansion hd g.H (normalizedAdjacency_isHermitian g.graph d)
    e hH T q z hz hq
  dsimp only [DeficientGraph.embeddedRetainedError] at hh
  rw [g.deletionNeighborhood_retained_boundaryDiagonal_zero o i j ell r hr,
    smul_zero, sub_zero] at hh
  exact hh

end RegularGraph
end LocalLaw
