import SpectralConsequences.AllCoreTreeExtension
import SpectralConsequences.GraphGreenEmbedding
import LocalLaw.GraphExcessSurgery
import LocalLaw.SourceReferenceIdentification

/-! A corrected reference class for possibly infinite deficient cores.
Complexity is expressed by its actual hereditary bounds on finite connected
induced cores. The diagonal estimate is relative to |md| on all of C+.
-/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
namespace SpectralConsequences
open LocalLaw
local instance allCoreReferenceThresholdDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace AllCoreGraph
variable {V : Type} [DecidableEq V] {d : ℕ}

/-- Actual finite induced restriction, retaining the original deficit. -/
def finiteRestriction (g : AllCoreGraph V d) (S : Finset V) : DeficientGraph S d where
  graph := g.graph.induce (S:Set V)
  deficit := fun v=>g.deficit v.val
  degree_deficit_le := by
    intro v
    have hcard := Nat.card_le_card_of_injective
      (fun w : (g.graph.induce (S:Set V)).neighborSet v =>
        (⟨w.val.val,w.property⟩:g.graph.neighborSet v.val))
      (by intro a b hab; apply Subtype.ext; apply Subtype.ext; exact congrArg (fun w : g.graph.neighborSet v.val=>w.val) hab)
    have hdegree : (g.graph.induce (S:Set V)).degree v≤g.graph.degree v.val := by
      simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using hcard
    exact (Nat.add_le_add_right hdegree _).trans (g.degree_deficit_le v.val)

/-- Finite complexity of an arbitrary core, formulated without infinite
edge-minus-vertex cardinal arithmetic. -/
def HereditaryBudget (g : AllCoreGraph V d) (ω : ℕ) : Prop :=
  ∀S:Finset V,(g.graph.induce (S:Set V)).Connected→
    (∑v:S,g.deficit v.val)+graphExcess (g.graph.induce (S:Set V))≤ω

/-- A finite deficient core viewed as a possibly infinite core. -/
def ofFinite [Fintype V] (g : DeficientGraph V d) : AllCoreGraph V d where
  graph := g.graph
  locallyFinite := inferInstance
  deficit := g.deficit
  degree_deficit_le := g.degree_deficit_le

omit [DecidableEq V] in
@[simp] theorem ofFinite_graph [Fintype V] (g : DeficientGraph V d) :
    (ofFinite g).graph=g.graph := rfl
omit [DecidableEq V] in
@[simp] theorem ofFinite_deficit [Fintype V] (g : DeficientGraph V d) (v : V) :
    (ofFinite g).deficit v=g.deficit v := rfl

omit [DecidableEq V] in
/-- The finite total complexity bound implies the hereditary condition used
for arbitrary cores. Both induced-connectivity hypotheses are genuine. -/
theorem ofFinite_hereditaryBudget [Fintype V] (g : DeficientGraph V d)
    (hconn : g.graph.Connected) (ω : ℕ)
    (hbudget : (∑v,g.deficit v)+graphExcess g.graph≤ω) :
    (ofFinite g).HereditaryBudget ω := by
  intro S hS
  have hex := connected_induce_graphExcess_le g.graph (S:Set V) hconn hS
  have hsum : (∑v:S,g.deficit v.val)≤∑v,g.deficit v := by
    rw [Finset.sum_coe_sort]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  have hh := (Nat.add_le_add hsum hex).trans hbudget
  simpa only [ofFinite,graphExcess,SimpleGraph.edgeFinset_card,←Nat.card_eq_fintype_card] using hh

/-- The two literal tree-extension graphs have the same vertices and edges;
only their locally-finite implementations differ. -/
def ofFinite_extensionIso [Fintype V] (g : DeficientGraph V d) :
    (ofFinite g).extension≃g g.treeExtension where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    intro x y
    cases x <;> cases y <;> rfl

omit [DecidableEq V] in
@[simp] theorem ofFinite_extensionIso_core [Fintype V] (g : DeficientGraph V d) (v : V) :
    ofFinite_extensionIso g (Sum.inl v)=Sum.inl v := rfl

/-- The finite and arbitrary-core constructions give the same genuine Green
function on every original finite-core vertex. -/
theorem ofFinite_green [Fintype V] (g : DeficientGraph V d) (hd : 3≤d)
    (z : ℂ) (hz : 0<z.im) (i j : V) :
    (ofFinite g).green (by omega) z i j=g.treeExtensionGreen (by omega) z i j := by
  have hh := green_eq_of_graph_iso (ofFinite g).extension g.treeExtension
    (ofFinite_extensionIso g) d ((ofFinite g).extension_degree_le (by omega))
    (g.treeExtension_degree_le (by omega)) z (ne_of_gt hz) (Sum.inl i) (Sum.inl j)
  simpa only [ofFinite_extensionIso_core,green,DeficientGraph.treeExtensionGreen] using hh.symm

omit [DecidableEq V] in
/-- Every finite connected induced restriction has the literal finite budget. -/
theorem finiteRestriction_budget (g : AllCoreGraph V d) {ω : ℕ}
    (hbudget : g.HereditaryBudget ω) (S : Finset V)
    (hS : (g.finiteRestriction S).graph.Connected) :
    (∑v,(g.finiteRestriction S).deficit v)+graphExcess (g.finiteRestriction S).graph≤ω :=
  hbudget S hS

end AllCoreGraph

/-- Reference bounds over every possibly infinite core of bounded hereditary
complexity, using the genuine ell2 Green function of its literal tree extension.
The relative diagonal estimate is valid on the unbounded upper half-plane. -/
def AllCoreReferenceThreshold (d ω : ℕ) (hd : 1≤d) : Prop :=
  ∃C:ℝ,1≤C ∧∀(V:Type)[DecidableEq V](g:AllCoreGraph V d),
    g.graph.Connected → g.HereditaryBudget ω→∀z:ℂ,0<z.im→
      (∀i j,‖g.green hd z i j‖≤C*‖-semicircleRoot z*treeEdgeWeight d‖^g.graph.dist i j) ∧
      (∀i j,|(g.green hd z i j).im|≤C*(kestenMcKayTransform d (semicircleRoot z) z).im) ∧
      (∀i,‖kestenMcKayTransform d (semicircleRoot z) z‖/C≤‖g.green hd z i i‖)

/-- Restricting the corrected all-core reference class to finite cores gives
exactly the finite class used by the local-law proof. This direction requires
no approximation theorem and no equality of threshold maxima. -/
theorem allCoreReferenceThreshold_imp_finite (d ω : ℕ) (hd : 3≤d)
    (hclass : AllCoreReferenceThreshold d ω (by omega)) :
    FiniteReferenceThreshold d ω := by
  obtain ⟨C,hC,h⟩ := hclass
  refine ⟨C,hC,?_⟩
  intro V _ _ g hconn hbudget z hz
  have href := h V (AllCoreGraph.ofFinite g) hconn
    (AllCoreGraph.ofFinite_hereditaryBudget g hconn ω hbudget) z hz
  simpa only [AllCoreGraph.ofFinite_graph,AllCoreGraph.ofFinite_green g hd z hz,
    g.treeExtensionGreen_eq_extensionGreen hd z hz] using href

theorem allCoreReferenceThreshold_le_finiteOmega (d ω : ℕ) (hd : 3≤d)
    (hclass : AllCoreReferenceThreshold d ω (by omega)) : ω≤finiteOmega d :=
  finiteOmega_maximal d hd ω (allCoreReferenceThreshold_imp_finite d ω hd hclass)

end SpectralConsequences

#print axioms SpectralConsequences.allCoreReferenceThreshold_imp_finite
#print axioms SpectralConsequences.allCoreReferenceThreshold_le_finiteOmega
