import LocalLaw.OptionalEdgeCutPrecision
import LocalLaw.FullEndpointMasks

/-! # Actual retained old edges and their genuine reference cut model -/

noncomputable section
namespace LocalLaw
local instance fullCoreMateModelDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type}

theorem fullOuterMate_unique (s : LabelledResamplingState V T ι) (selector : ℕ) (S : Set V)
    (i j : s.AdmissibleSampleIndex selector) (k : s.fullCoreMask S)
    (hi : s.fullOuterMate selector S i = some k) (hj : s.fullOuterMate selector S j = some k) : i = j := by
  have hi' := (s.fullOuterMate_eq_some selector S i k).mp hi
  have hj' := (s.fullOuterMate_eq_some selector S j k).mp hj
  exact (s.admissibleBoundary_eq_iff selector i j).mp (Subtype.ext (hi'.trans hj'.symm))

theorem fullInnerOuterMate_disjoint (s : LabelledResamplingState V T ι) (selector : ℕ) (S : Set V)
    (i j : s.AdmissibleSampleIndex selector) (k : s.fullCoreMask S)
    (hi : s.fullInnerMate selector S i = some k) : s.fullOuterMate selector S j ≠ some k := by
  intro hj
  have hi' := (s.fullInnerMate_eq_some selector S i k).mp hi
  have hj' := (s.fullOuterMate_eq_some selector S j k).mp hj
  exact (s.admissibleBoundaryVertex selector j).property
    ((hj'.trans hi'.symm) ▸ sampledSwitching_root_mem s.graph T s.samples (s.boundary i.val))

theorem fullRetainedMates_old_edge (s : LabelledResamplingState V T ι) (selector : ℕ) (S : Set V)
    (i : s.AdmissibleSampleIndex selector) (x y : s.fullCoreMask S)
    (hx : s.fullInnerMate selector S i = some x) (hy : s.fullOuterMate selector S i = some y) :
    s.graph.Adj (s.fullCoreEmbedding S x).val (s.fullCoreEmbedding S y).val := by
  have hx' := (s.fullInnerMate_eq_some selector S i x).mp hx
  have hy' := (s.fullOuterMate_eq_some selector S i y).mp hy
  have he : s.graph.Adj (s.quad i.val).a (s.admissibleBoundaryVertex selector i).val :=
    (s.boundary i.val).property.1
  simpa only [hx',hy'] using he

end LabelledResamplingState
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

def fullCoreEdgeCutModel (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (S : Set (Fin N)) : DeficientGraph S d :=
  let s := g.admissibleState T labels samples
  (g.deficient.restrict S).optionalEdgeCut (s.fullCoreEmbedding S)
    (s.fullInnerMate selector S) (s.fullOuterMate selector S)

omit [Fintype ι] in
theorem fullCoreEdgeCut_reference_budget (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (S : Set (Fin N)) (hb : (g.deficient.restrict S).ComponentFiniteReferenceBudget) :
    (g.fullCoreEdgeCutModel T labels samples selector S).ComponentFiniteReferenceBudget :=
  (g.deficient.restrict S).optionalEdgeCut_reference_budget _ _ _ hb

theorem fullCoreEdgeCut_retained_inverse (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector : ℕ) (S : Set (Fin N))
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let s := g.admissibleState T labels samples
    let e := s.fullCoreEmbedding S
    let P := ((g.deficient.restrict S).extensionGreen q z).submatrix e e
    let A : Matrix (s.fullCoreMask S) (s.fullCoreMask S) ℂ :=
      P⁻¹ - fullQuadRetainedEdges (s.fullInnerMate selector S) (s.fullOuterMate selector S) (treeEdgeWeight d) -
        Matrix.diagonal (fun k => q * treeEdgeWeight d ^ 2 *
          fullQuadRetainedDegree (s.fullInnerMate selector S) (s.fullOuterMate selector S) k)
    IsUnit A ∧ A⁻¹ = ((g.fullCoreEdgeCutModel T labels samples selector S).extensionGreen q z).submatrix e e := by
  dsimp only
  let s := g.admissibleState T labels samples
  exact (g.deficient.restrict S).optionalEdgeCut_retained_inverse hd (s.fullCoreEmbedding S)
    (s.fullInnerMate selector S) (s.fullOuterMate selector S)
    (s.fullOuterMate_unique selector S) (s.fullInnerOuterMate_disjoint selector S)
    (s.fullRetainedMates_old_edge selector S) q z hz hq

omit [Fintype ι] in
theorem fullCoreEdgeCut_intrinsic_diameter (g : RegularGraph N d)
    (T : Set (Fin N)) (labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector : ℕ) (S : Set (Fin N))
    (hb : (g.deficient.restrict S).ComponentFiniteReferenceBudget) (R : ℕ)
    (hR : ∀ x y, (g.graph.induce S).dist x y ≤ R) (x y : S) :
    (g.fullCoreEdgeCutModel T labels samples selector S).graph.dist x y ≤ hereditaryReferenceRadius d R :=
  (g.deficient.restrict S).edgeSubgraph_intrinsic_diameter _ sdiff_le hb R hR x y

end RegularGraph
end LocalLaw
