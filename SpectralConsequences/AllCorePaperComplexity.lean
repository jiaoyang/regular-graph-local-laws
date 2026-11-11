import SpectralConsequences.AllCoreReferenceThreshold
import LocalLaw.CycleSpaceCounting
import LocalLaw.GeneralExcessSurgery

/-! # The paper's finite deficit-plus-feedback-edge complexity

For an arbitrary core, a finite set of actual edges whose removal leaves a
forest and a finite set supporting the deficit give the literal complexity
bound used in the article. This bound implies every finite induced-core
budget. Conversely, every finite connected core has a witness with exactly
its Euler excess, obtained from an actual spanning tree.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace SpectralConsequences
open LocalLaw
local instance allCorePaperComplexityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem finite_forest_graphExcess_eq_zero {A : Type*} [Fintype A]
    (G : SimpleGraph A) (hforest : G.IsAcyclic) : graphExcess G=0 := by
  rw [graphExcess_eq_sum_components]
  apply Finset.sum_eq_zero
  intro C _
  have ht : (G.induce C.supp).IsTree :=
    ⟨C.connected_induce_supp,graph_acyclic_induce G C.supp hforest⟩
  have he := connected_graph_excess_euler (G.induce C.supp) ht.isConnected
  have hc := (SimpleGraph.isTree_iff_connected_and_card.mp ht).2
  simp only [graphExcess,graphEdgeCount,SimpleGraph.edgeFinset_card,←Nat.card_eq_fintype_card] at he ⊢
  omega

namespace AllCoreGraph
variable {V : Type} [DecidableEq V] {d : ℕ}

structure PaperComplexityWitness (g : AllCoreGraph V d) (ω : ℕ) where
  deficitSet : Finset V
  deficit_zero : ∀ v, v ∉ deficitSet → g.deficit v = 0
  feedbackEdges : Finset (Sym2 V)
  feedback_actual : ∀e∈feedbackEdges,e∈g.graph.edgeSet
  feedback_forest : (g.graph.deleteEdges (feedbackEdges:Set (Sym2 V))).IsAcyclic
  budget : (∑v∈deficitSet,g.deficit v)+feedbackEdges.card≤ω

def PaperComplexity (g : AllCoreGraph V d) (ω : ℕ) : Prop := Nonempty (g.PaperComplexityWitness ω)

theorem finite_induced_feedback_edge_count (_G : SimpleGraph V)
    (F : Finset (Sym2 V)) (S : Finset V) :
    graphEdgeCount ((SimpleGraph.fromEdgeSet (F:Set (Sym2 V))).induce (S:Set V))≤F.card := by
  let K := SimpleGraph.fromEdgeSet (F:Set (Sym2 V))
  let f : K.induce (S:Set V) →g K := ⟨Subtype.val,fun h=>h⟩
  have hfirst : graphEdgeCount (K.induce (S:Set V))≤Nat.card K.edgeSet :=
    Nat.card_le_card_of_injective f.mapEdgeSet (SimpleGraph.Hom.mapEdgeSet.injective f Subtype.val_injective)
  let incl : K.edgeSet → F := fun e=>⟨e.val,by
    have hh : e.val∈(F:Set (Sym2 V))\{e|e.IsDiag} := by
      simpa only [K,SimpleGraph.edgeSet_fromEdgeSet] using e.property
    exact hh.1⟩
  have hsecond := Nat.card_le_card_of_injective incl (by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun q : F => q.val) h)
  exact hfirst.trans (by simpa using hsecond)

theorem induced_excess_le_feedback (G : SimpleGraph V) (F : Finset (Sym2 V))
    (hactual : ∀e∈F,e∈G.edgeSet)
    (hforest : (G.deleteEdges (F:Set (Sym2 V))).IsAcyclic) (S : Finset V) :
    graphExcess (G.induce (S:Set V))≤F.card := by
  let A := (G.deleteEdges (F:Set (Sym2 V))).induce (S:Set V)
  let K := (SimpleGraph.fromEdgeSet (F:Set (Sym2 V))).induce (S:Set V)
  have hsup : G.induce (S:Set V)=A⊔K := by
    ext u v
    change G.Adj u.val v.val ↔
      (G.deleteEdges (F:Set (Sym2 V))).Adj u.val v.val ∨
      (SimpleGraph.fromEdgeSet (F:Set (Sym2 V))).Adj u.val v.val
    simp only [SimpleGraph.deleteEdges_adj,SimpleGraph.fromEdgeSet_adj]
    constructor
    · intro huv
      by_cases hF:s(u.val,v.val)∈F
      · exact Or.inr ⟨hF,huv.ne⟩
      · exact Or.inl ⟨huv,hF⟩
    · rintro (h|h)
      · exact h.1
      · exact hactual _ h.1
  have hzero : graphExcess A=0 := finite_forest_graphExcess_eq_zero A
    (graph_acyclic_induce _ _ hforest)
  rw [hsup]
  exact (graphExcess_sup_le A K).trans (by
    simpa only [hzero,zero_add] using finite_induced_feedback_edge_count G F S)

theorem PaperComplexityWitness.hereditary {g : AllCoreGraph V d} {ω : ℕ}
    (w : g.PaperComplexityWitness ω) : g.HereditaryBudget ω := by
  intro S _
  have hsum : (∑v:S,g.deficit v.val)≤∑v∈w.deficitSet,g.deficit v := by
    rw [Finset.sum_coe_sort]
    have heq : (∑v∈S∩w.deficitSet,g.deficit v)=∑v∈S,g.deficit v := by
      apply Finset.sum_subset Finset.inter_subset_left
      intro v hvS hnot
      apply w.deficit_zero
      intro hv
      exact hnot (Finset.mem_inter.mpr ⟨hvS,hv⟩)
    rw [←heq]
    exact Finset.sum_le_sum_of_subset Finset.inter_subset_right
  have hex := induced_excess_le_feedback g.graph w.feedbackEdges w.feedback_actual w.feedback_forest S
  exact (Nat.add_le_add hsum hex).trans w.budget

theorem PaperComplexity.hereditary {g : AllCoreGraph V d} {ω : ℕ}
    (h : g.PaperComplexity ω) : g.HereditaryBudget ω := by
  obtain ⟨w⟩:=h
  exact w.hereditary

theorem ofFinite_paperComplexity [Fintype V] (g : DeficientGraph V d)
    (hconn : g.graph.Connected) (ω : ℕ)
    (hbudget : (∑v,g.deficit v)+graphExcess g.graph≤ω) :
    (ofFinite g).PaperComplexity ω := by
  obtain ⟨T,hTG,hT⟩:=hconn.exists_isTree_le
  let F := (g.graph\T).edgeFinset
  have hFcard : F.card=graphExcess g.graph := by
    simpa only [F,SimpleGraph.edgeFinset_card,←Nat.card_eq_fintype_card] using
      off_tree_edge_count g.graph T hconn hTG hT
  have hFactual : ∀e∈F,e∈g.graph.edgeSet := by
    intro e he
    have hh : e∈(g.graph\T).edgeSet := by simpa only [F,SimpleGraph.mem_edgeFinset] using he
    rw [SimpleGraph.edgeSet_sdiff] at hh
    exact hh.1
  have hdelete : g.graph.deleteEdges (F:Set (Sym2 V))=T := by
    ext u v
    simp only [SimpleGraph.deleteEdges_adj,Finset.mem_coe,F,
      SimpleGraph.mem_edgeFinset,SimpleGraph.sdiff_adj]
    constructor
    · rintro ⟨huv,hn⟩
      by_contra ht
      exact hn ⟨huv,ht⟩
    · intro huv
      exact ⟨hTG huv,fun h=>h.2 huv⟩
  refine ⟨⟨Finset.univ,?_,F,hFactual,?_,?_⟩⟩
  · intro v hv
    exact (hv (Finset.mem_univ v)).elim
  · change (g.graph.deleteEdges (F:Set (Sym2 V))).IsAcyclic
    rw [hdelete]
    exact hT.IsAcyclic
  · simpa only [ofFinite_deficit,hFcard] using hbudget

end AllCoreGraph
end SpectralConsequences
