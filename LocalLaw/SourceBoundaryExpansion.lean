import LocalLaw.SourceBoundarySchur
import LocalLaw.EmbeddedCutIncidence
import LocalLaw.BoundaryDiagonalExpansion

/-!
# Actual boundary-observation expansion in the finite source neighborhood

The full physical and finite deleted kernels are compared on the same actual
boundary-edge labels. All cut incidence and retained-boundary hypotheses are
proved from the literal neighborhood geometry. The resulting three terms
are the diagonal observation sum, off-diagonal error, and nonlinear remainder
in source (6.24).
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceBoundaryExpansionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace RegularGraph
variable {N d : ℕ}

private theorem neighborhood_captures_incident (g : RegularGraph N d) (o i j : Fin N) (ell r : ℕ)
    (hr : 1 ≤ r) :
    let e : deletionNeighborhoodVertices g.graph o i j ell r ↪ Fin N := Function.Embedding.subtype _
    ∀ x : deletionNeighborhoodInnerSet g.graph o i j ell r, ∀ a,
      a ∉ Set.range e → g.H (e x.val) a = 0 := by
  dsimp only
  intro x a ha
  have hx := (deletionNeighborhood_inner_mem g.graph o i j ell r x.val).mp x.property
  have hnonadj : ¬g.graph.Adj x.val.val a := by
    intro h
    have hmem := deletionNeighborhood_contains_schur_ball g.graph o i j x.val.val ell r (Or.inl hx)
      ((SimpleGraph.edist_le (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil)).trans
        (by simpa using (ENat.coe_le_coe.mpr hr)))
    exact ha ⟨⟨a, hmem⟩, rfl⟩
  simp [H, normalizedAdjacency, SimpleGraph.adjMatrix_apply, hnonadj]

/-- The actual source self-energy is a sandwich of the difference of genuine
deleted kernels on common boundary labels, with no factorization premise. -/
theorem deletionNeighborhood_boundary_expansion (g : RegularGraph N d) (hd : 3 ≤ d)
    (o i j : Fin N) (ell r : ℕ) (hr : 1 ≤ r) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let M := g.deletionNeighborhoodModel o i j ell r
    let T := deletionNeighborhoodInnerSet g.graph o i j ell r
    let e : deletionNeighborhoodVertices g.graph o i j ell r ↪ Fin N := Function.Embedding.subtype _
    let R := ((g.G z).submatrix e e).submatrix (Subtype.val : T → _) (Subtype.val : T → _)
    let P := (M.extensionGreen q z).submatrix (Subtype.val : T → _) (Subtype.val : T → _)
    let U := cutInnerCoupling M.graph d T
    let D := ((green (g.H.submatrix (Subtype.val : ((e '' T)ᶜ : Set (Fin N)) → Fin N)
      (Subtype.val : ((e '' T)ᶜ : Set (Fin N)) → Fin N)) z).submatrix
        (outsideImageEmbedding e T) (outsideImageEmbedding e T) -
      (M.delete T).extensionGreen q z).submatrix
        (boundaryOutsideVertex M.graph T) (boundaryOutsideVertex M.graph T)
    R - P = (P * U) * D * (U.transpose * P) + (R - P) * U * D * U.transpose * P := by
  dsimp only
  let M := g.deletionNeighborhoodModel o i j ell r
  let T := deletionNeighborhoodInnerSet g.graph o i j ell r
  let e : deletionNeighborhoodVertices g.graph o i j ell r ↪ Fin N := Function.Embedding.subtype _
  have hH : M.H = g.H.submatrix e e := normalizedAdjacency_induce g.graph d _
  have hself := M.embeddedSelfEnergy_sub_retainedSelfEnergy g.H (normalizedAdjacency_isHermitian g.graph d)
    e hH T q z (g.neighborhood_captures_incident o i j ell r hr)
  have hh := g.deletionNeighborhood_retained_expansion hd o i j ell r hr q z hz hq
  dsimp only at hh
  rw [hself] at hh
  simpa only [Matrix.mul_assoc] using hh

/-- Literal source (6.24)'s three-term row bound, with genuine physical
resolvents and actual boundary labels. The terms still require their source
concentration, off-diagonal and nonlinear estimates. -/
theorem deletionNeighborhood_boundary_row_three_term (g : RegularGraph N d) (hd : 3 ≤ d)
    (o i j : Fin N) (ell r : ℕ) (hr : 1 ≤ r) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (x y : deletionNeighborhoodInnerSet g.graph o i j ell r) :
    let M := g.deletionNeighborhoodModel o i j ell r
    let T := deletionNeighborhoodInnerSet g.graph o i j ell r
    let e : deletionNeighborhoodVertices g.graph o i j ell r ↪ Fin N := Function.Embedding.subtype _
    let R := ((g.G z).submatrix e e).submatrix (Subtype.val : T → _) (Subtype.val : T → _)
    let P := (M.extensionGreen q z).submatrix (Subtype.val : T → _) (Subtype.val : T → _)
    let U := cutInnerCoupling M.graph d T
    let D := ((green (g.H.submatrix (Subtype.val : ((e '' T)ᶜ : Set (Fin N)) → Fin N)
      (Subtype.val : ((e '' T)ᶜ : Set (Fin N)) → Fin N)) z).submatrix
        (outsideImageEmbedding e T) (outsideImageEmbedding e T) -
      (M.delete T).extensionGreen q z).submatrix
        (boundaryOutsideVertex M.graph T) (boundaryOutsideVertex M.graph T)
    ‖R x y - P x y‖ ≤
      ‖∑ a, (P * U) x a * (U.transpose * P) a y * D a a‖ +
      ‖∑ a, ∑ b ∈ (Finset.univ.erase a), (P * U) x a * D a b * (U.transpose * P) b y‖ +
      ‖((R - P) * U * D * U.transpose * P) x y‖ := by
  dsimp only
  have hh := g.deletionNeighborhood_boundary_expansion hd o i j ell r hr q z hz hq
  dsimp only at hh
  have hentry := congrArg (fun A => A x y) hh
  dsimp only at hentry
  rw [Matrix.sub_apply, Matrix.add_apply, boundary_sandwich_diagonal_split] at hentry
  rw [hentry]
  exact (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)

end RegularGraph
end LocalLaw
