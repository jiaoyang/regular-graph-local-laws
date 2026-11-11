import LocalLaw.TruncatedTreeCavity
import LocalLaw.SourceResamplingStructural

/-! # The old truncated T reference and all its minors are sample independent

The actual resampling preserves the induced graph on T. Both regular graph
models carry zero source deficit there, so the deficient models themselves
are equal, including their genuine boundary operators and inverse matrices.
-/

noncomputable section
namespace LocalLaw
local instance truncatedReferencePreservationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem deficientGraph_eq_of_graph_deficit {V : Type*} [Fintype V] {d : ℕ}
    (g h : DeficientGraph V d) (hgraph : g.graph = h.graph) (hδ : g.deficit = h.deficit) : g = h := by
  cases g with
  | mk G δ hg =>
    cases h with
    | mk H ε hh =>
      cases hgraph
      cases hδ
      rfl

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem resampled_truncated_model_eq (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T) (selector : ℕ) :
    (g.labelledResampledGraph T labels samples selector).deficient.restrict T = g.deficient.restrict T := by
  apply deficientGraph_eq_of_graph_deficit
  · exact (g.admissibleState T labels samples).fullResample_induce selector
  · rfl

theorem resampled_truncated_extensionGreen_eq (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (q z : ℂ) :
    ((g.labelledResampledGraph T labels samples selector).deficient.restrict T).extensionGreen q z =
      (g.deficient.restrict T).extensionGreen q z :=
  congrArg (fun M : DeficientGraph T d => M.extensionGreen q z) (g.resampled_truncated_model_eq T labels samples selector)

theorem resampled_truncated_minor_extensionGreen_eq (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (j : T) (q z : ℂ) :
    (((g.labelledResampledGraph T labels samples selector).deficient.restrict T).deleteVertex j).extensionGreen q z =
      ((g.deficient.restrict T).deleteVertex j).extensionGreen q z :=
  congrArg (fun M : DeficientGraph T d => (M.deleteVertex j).extensionGreen q z)
    (g.resampled_truncated_model_eq T labels samples selector)

end RegularGraph
end LocalLaw
