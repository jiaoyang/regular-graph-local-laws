import LocalLaw.AllCentralTreeCavity
import LocalLaw.BoundaryBlockPreservation
import LocalLaw.CentralReferenceIndependence
import LocalLaw.SourceBoundaryDefect
import LocalLaw.TruncatedBoundarySchur

/-! # The actual tree-case T-Schur boundary defect

In an original tree ball every finite model boundary entry is the scalar
cavity iterate times the identity. The physical defect relative to Ext(T,q)
is therefore the canonical endpoint defect plus the explicit scalar Y-q.
-/

noncomputable section
namespace LocalLaw
local instance treeCavityBoundaryDefectDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

def sourceTruncatedBoundaryDefect (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector : ℕ) (q z : ℂ) : Matrix ι ι ℂ :=
  (g.sourceEndpointT T labels S selector z).submatrix
    ((g.admissibleState T labels S).endpointFinalBoundaryRoot selector)
    ((g.admissibleState T labels S).endpointFinalBoundaryRoot selector) - q • 1

theorem sourceTruncatedBoundaryDefect_eq_actual (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector : ℕ) (q z : ℂ) :
    let s := g.admissibleState T labels S
    g.sourceTruncatedBoundaryDefect T labels S selector q z =
      ((g.labelledResampledGraph T labels S selector).truncatedBoundaryDefect T q z).submatrix
        (s.fullResample selector).boundary (s.fullResample selector).boundary := by
  dsimp only
  let s := g.admissibleState T labels S
  ext i j
  simp only [sourceTruncatedBoundaryDefect, sourceEndpointT, truncatedBoundaryDefect,
    Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hi := s.endpointFinalBoundaryRoot_outer selector i
  have hj := s.endpointFinalBoundaryRoot_outer selector j
  change ((g.labelledResampledGraph T labels S selector).deficient.delete T).G z
      (s.endpointFinalBoundaryRoot selector i).val (s.endpointFinalBoundaryRoot selector j).val -
      q * (if i = j then 1 else 0) = _
  rw [hi, hj]
  have heq : ((g.admissibleState T labels S).fullResample selector).boundary i =
      ((g.admissibleState T labels S).fullResample selector).boundary j ↔ i = j :=
    ((g.admissibleState T labels S).fullResample selector).boundary.injective.eq_iff
  simp only [heq]
  rfl

theorem sourceEndpointQ_tree_boundary_block (g : RegularGraph N d) (hd : 3 ≤ d) (o : Fin N)
    (ell selector r R : ℕ) (hsep : 2 * r + 2 ≤ selector) (hr : r + 2 ≤ selector)
    (hmargin : ell + r + 1 ≤ R) (hTree : (graphBall g.graph o R).IsTree)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let T := graphBallVertices g.graph o ell
    let s := g.admissibleState T labels S
    (g.sourceEndpointQ T labels S selector r q z).submatrix
      (s.endpointFinalBoundaryRoot selector) (s.endpointFinalBoundaryRoot selector) =
      cavityIterate z q (r + 1) • 1 := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T labels S
  ext i j
  have hs := g.sourceEndpoint_boundary_block_preserved hd T labels S selector r hsep hr q z hz hq i j
  have hc := g.endpointModel_boundary_eq_central hd T labels S selector r hsep q z hz hq (labels i) (labels j)
  have hY := g.tree_central_boundary_block hd o ell r R hmargin hTree (labels i) (labels j) q z hz hq
  dsimp only at hs hc hY
  have he := hs.trans (hc.trans hY)
  simpa only [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, labels.injective.eq_iff] using he

/-- Exact source-(6.35) defect decomposition. The finite scalar correction
is explicit and can be bounded by the separately proved residual estimate. -/
theorem sourceTruncatedBoundaryDefect_tree_decomposition (g : RegularGraph N d) (hd : 3 ≤ d) (o : Fin N)
    (ell selector r R : ℕ) (hsep : 2 * r + 2 ≤ selector) (hr : r + 2 ≤ selector)
    (hmargin : ell + r + 1 ≤ R) (hTree : (graphBall g.graph o R).IsTree)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let T := graphBallVertices g.graph o ell
    g.sourceTruncatedBoundaryDefect T labels S selector q z =
      g.sourceBoundaryDefect T labels S selector r q z + (cavityIterate z q (r + 1) - q) • 1 := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T labels S
  have hQ := g.sourceEndpointQ_tree_boundary_block hd o ell selector r R hsep hr hmargin hTree labels S q z hz hq
  dsimp only at hQ
  ext i j
  have hQij := congrFun (congrFun hQ i) j
  simp only [Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul] at hQij
  simp only [sourceTruncatedBoundaryDefect, sourceBoundaryDefect, Matrix.submatrix_apply,
    Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hQij]
  ring

end RegularGraph
end LocalLaw
