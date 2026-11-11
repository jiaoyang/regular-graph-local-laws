import LocalLaw.SelectedFirstGreen
import LocalLaw.SourceMinorPerturbation

/-!
# Removing every selected first vertex erases the entire outside surgery

Every actual changed outside edge meets a selected sampled first vertex.
After those vertices are removed, the old and new physical graphs agree.
Their inherited deficits also agree, since both actual source models remain
saturated. Thus the full deficient models, not just their adjacency, agree.
-/

noncomputable section
namespace LocalLaw
local instance selectedFirstDeletionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type} [Fintype ι]

def selectedFirstSet (s : LabelledResamplingState V T ι) (selector : ℕ) : Set (Tᶜ : Set V) :=
  Set.range (s.selectedFirstEmbedding selector)

theorem fullResample_without_selectedFirst_adj (s : LabelledResamplingState V T ι) (selector : ℕ)
    (x y : ((s.selectedFirstSet selector)ᶜ : Set (Tᶜ : Set V))) :
    (s.fullResample selector).graph.Adj x.val.val y.val.val ↔ s.graph.Adj x.val.val y.val.val := by
  rw [s.fullResample_graph_eq_applySwitches selector]
  apply applySwitches_adj_of_no_footprints
  intro q hq
  obtain ⟨i, _, hi, hqi⟩ := (s.mem_selectedQuads selector _ q).mp hq
  subst q
  have hroot := sampledSwitching_root_mem s.graph T s.samples (s.boundary i)
  have hxa : x.val.val ≠ (s.quad i).a := fun h => x.val.property (h ▸ hroot)
  have hya : y.val.val ≠ (s.quad i).a := fun h => y.val.property (h ▸ hroot)
  have hxb : x.val.val ≠ (s.quad i).c := by
    intro h
    exact x.property ⟨⟨i, hi⟩, Subtype.ext h.symm⟩
  have hyb : y.val.val ≠ (s.quad i).c := by
    intro h
    exact y.property ⟨⟨i, hi⟩, Subtype.ext h.symm⟩
  exact (s.quad i).no_footprint_after_removing_roots _ _ hxa hya hxb hyb

theorem fullResample_outside_delete_selectedFirst_graph (s : LabelledResamplingState V T ι)
    (selector : ℕ) :
    (outsideGraph (s.fullResample selector).graph T).induce (s.selectedFirstSet selector)ᶜ =
      (outsideGraph s.graph T).induce (s.selectedFirstSet selector)ᶜ := by
  ext x y
  exact s.fullResample_without_selectedFirst_adj selector x y

end LabelledResamplingState

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

omit [DecidableEq V] in
theorem eq_of_graph_and_deficit_eq (g h : DeficientGraph V d)
    (hgraph : g.graph = h.graph) (hdeficit : g.deficit = h.deficit) : g = h := by
  cases g
  cases h
  cases hgraph
  cases hdeficit
  rfl

omit [DecidableEq V] in
theorem delete_deficit_eq_of_saturated (g : DeficientGraph V d)
    (hsat : ∀ v, g.graph.degree v + g.deficit v = d) (S : Set V) (v : (Sᶜ : Set V)) :
    (g.delete S).deficit v = d - (g.delete S).graph.degree v := by
  have hh := hsat v.val
  change g.deficit v.val + g.graph.degree v.val - (g.graph.induce Sᶜ).degree v =
    d - (g.graph.induce Sᶜ).degree v
  omega

end DeficientGraph

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem labelledResampled_delete_selectedFirst_eq (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) :
    let s := g.admissibleState T boundary samples
    let W := s.selectedFirstSet selector
    ((g.labelledResampledGraph T boundary samples selector).deficient.delete T).delete W =
      (g.deficient.delete T).delete W := by
  dsimp only
  let s := g.admissibleState T boundary samples
  let W := s.selectedFirstSet selector
  let old := g.deficient.delete T
  let new := (g.labelledResampledGraph T boundary samples selector).deficient.delete T
  have hgraph : (new.delete W).graph = (old.delete W).graph :=
    s.fullResample_outside_delete_selectedFirst_graph selector
  apply DeficientGraph.eq_of_graph_and_deficit_eq _ _ hgraph
  funext v
  rw [new.delete_deficit_eq_of_saturated
    ((g.labelledResampledGraph T boundary samples selector).deleted_degree_deficit_saturated T),
    old.delete_deficit_eq_of_saturated (g.deleted_degree_deficit_saturated T), hgraph]

end RegularGraph
end LocalLaw
