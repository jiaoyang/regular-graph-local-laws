import SpectralConsequences.AllCoreTreeExtension
import LocalLaw.GraphDirichletOperatorLimit

/-! Finite induced cores on the original ambient vertex set. Vertices outside
the finite core are isolated with full deficit, hence acquire no tree slots. -/
open scoped BigOperators
open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance finiteSupportDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace AllCoreGraph
variable {V : Type} [DecidableEq V] {d : ℕ}

def finiteSupport (g : AllCoreGraph V d) (S : Finset V) : AllCoreGraph V d where
  graph := g.graph.finiteDirichletRestriction S
  locallyFinite := inferInstance
  deficit v := if v∈S then g.deficit v else d
  degree_deficit_le := by
    intro v
    by_cases hv : v∈S
    · simp only [if_pos hv]
      exact (Nat.add_le_add_right (g.graph.finiteDirichletRestriction_degree_le S v) _).trans
        (g.degree_deficit_le v)
    · have hzero : (g.graph.finiteDirichletRestriction S).degree v=0 := by
        change ((g.graph.finiteDirichletRestriction S).neighborFinset v).card=0
        simp [g.graph.finiteDirichletRestriction_neighborFinset,hv]
      simp [hv,hzero]

theorem finiteSupport_deficit (g : AllCoreGraph V d) (S : Finset V) (v : V) (hv : v∈S) :
    (g.finiteSupport S).deficit v=g.deficit v := by simp [finiteSupport,hv]

theorem finiteSupport_neighbors (g : AllCoreGraph V d) (S : Finset V) (v : V)
    (hv : v∈S) (hstar : g.graph.neighborFinset v⊆S) :
    (g.finiteSupport S).graph.neighborFinset v=g.graph.neighborFinset v := by
  change (g.graph.finiteDirichletRestriction S).neighborFinset v=_
  rw [g.graph.finiteDirichletRestriction_neighborFinset,if_pos hv]
  exact Finset.inter_eq_left.mpr hstar

theorem finiteSupport_neighbors_eventually (g : AllCoreGraph V d) (S : ℕ→Finset V)
    (hstar : ∀v,∀ᶠ n in atTop,v∈S n ∧ g.graph.neighborFinset v⊆S n) :
    ∀v,∀ᶠ n in atTop,(g.finiteSupport (S n)).graph.neighborFinset v=g.graph.neighborFinset v := by
  intro v
  filter_upwards [hstar v] with n hn
  exact g.finiteSupport_neighbors (S n) v hn.1 hn.2

theorem finiteSupport_deficit_eventually (g : AllCoreGraph V d) (S : ℕ→Finset V)
    (hmem : ∀v,∀ᶠ n in atTop,v∈S n) :
    ∀v,∀ᶠ n in atTop,(g.finiteSupport (S n)).deficit v=g.deficit v := by
  intro v
  filter_upwards [hmem v] with n hn
  exact g.finiteSupport_deficit (S n) v hn

end AllCoreGraph
end SpectralConsequences
