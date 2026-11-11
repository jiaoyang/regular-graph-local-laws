import LocalLaw.SourceRetainedExpansion
import LocalLaw.ActualBoundaryWeights

/-! # The fixed Schur diagonal weights are the actual concentration weights -/

noncomputable section
set_option maxHeartbeats 1600000
namespace LocalLaw
local instance sourceRetainedWeightsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem mul_sourceCutCoupling {I : Type*} (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (A : Matrix I T ℂ) (i : I) (a : ι) :
    (A * g.sourceCutCoupling T labels) i a =
      (↑((Real.sqrt ((d : ℝ) - 1))⁻¹) : ℂ) * A i (cutInsideVertex g.graph T (labels a)) := by
  change (A * cutInnerCoupling g.graph d T) i (labels a) = _
  exact mul_cutInnerCoupling g.graph d T A i (labels a)

omit [Fintype ι] in
theorem transpose_sourceCutCoupling_mul {J : Type*} (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (B : Matrix T J ℂ) (a : ι) (j : J) :
    ((g.sourceCutCoupling T labels).transpose * B) a j =
      (↑((Real.sqrt ((d : ℝ) - 1))⁻¹) : ℂ) * B (cutInsideVertex g.graph T (labels a)) j := by
  change ((cutInnerCoupling g.graph d T).transpose * B) (labels a) j = _
  exact transpose_cutInnerCoupling_mul g.graph d T B (labels a) j

theorem sourceRetainedReference_isSymm (g : RegularGraph N d) (T : Set (Fin N))
    (r : ℕ) (q z : ℂ) : (g.sourceRetainedReference T r q z).IsSymm :=
  ((g.filledExteriorModel T (centralBoundaryVertices g.graph T r)).extensionGreen_isSymm q z).submatrix
    (fun x => (filledExteriorInnerEquiv T (centralBoundaryVertices g.graph T r)).symm x |>.val)

omit [Fintype ι] in
/-- The exact diagonal Schur weight is the deterministic old Green-product
weight used by actual one-edge concentration, including edge normalization. -/
theorem sourceRetained_diagonal_weight (g : RegularGraph N d) (o : Fin N) (ell r : ℕ)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (q z : ℂ) (y : graphBallVertices g.graph o ell) (a : ι) :
    let T := graphBallVertices g.graph o ell
    let S := filledExteriorVertices T (centralBoundaryVertices g.graph T r)
    let hS := filledExterior_contains_inner T (centralBoundaryVertices g.graph T r)
    let root : T := ⟨o, center_mem_graphBall g.graph o ell⟩
    let P := g.sourceRetainedReference T r q z
    let U := g.sourceCutCoupling T labels
    (P * U) root a * (U.transpose * P) a y =
      (↑((Real.sqrt ((d : ℝ) - 1))⁻¹) : ℂ) ^ 2 *
        g.deficient.boundaryProductWeight S o ell hS q z ⟨y.val, hS y.property⟩ (labels a) := by
  dsimp only
  rw [g.mul_sourceCutCoupling, g.transpose_sourceCutCoupling_mul,
    (g.sourceRetainedReference_isSymm _ r q z).apply y (cutInsideVertex g.graph _ (labels a))]
  unfold DeficientGraph.boundaryProductWeight
  dsimp only [sourceRetainedReference, filledRetainedGreen, filledExteriorModel,
    filledExteriorInnerEquiv, inducedBoundaryInner, Matrix.submatrix_apply, Equiv.symm, cutInsideVertex]
  ring_nf
  rfl


/-- Single retained entries are values of the fixed ordinary expanded-ball
model, with its actual original inherited zero deficit. -/
theorem sourceRetainedReference_entry_ball (g : RegularGraph N d) (o : Fin N) (ell r : ℕ)
    (q z : ℂ) (x y : graphBallVertices g.graph o ell) :
    g.sourceRetainedReference (graphBallVertices g.graph o ell) r q z x y =
      (g.deficient.restrict (graphBallVertices g.graph o (ell+r+1))).extensionGreen q z
        ⟨x.val, graphBallVertices_mono g.graph o (by omega) x.property⟩
        ⟨y.val, graphBallVertices_mono g.graph o (by omega) y.property⟩ := by
  have hset := filled_centralBoundary_eq_ball g.graph o ell r
  have hcongr (S L : Set (Fin N)) (h : S = L) (u v : Fin N)
      (huS : u ∈ S) (hvS : v ∈ S) (huL : u ∈ L) (hvL : v ∈ L) :
      (g.deficient.restrict S).extensionGreen q z ⟨u, huS⟩ ⟨v, hvS⟩ =
        (g.deficient.restrict L).extensionGreen q z ⟨u, huL⟩ ⟨v, hvL⟩ := by
    subst L
    rfl
  exact hcongr _ _ hset x.val y.val _ _ _ _

end RegularGraph
end LocalLaw
