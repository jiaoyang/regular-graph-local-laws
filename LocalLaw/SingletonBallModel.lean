import LocalLaw.VertexDeletionModel
import LocalLaw.NeighborhoodPairIdentities
import LocalLaw.CutComponentDiameter

/-!
# The genuine common ball for an adjacent singleton observation

A radius-(r+1) ball around one endpoint contains every radius-r pair model
at the two endpoints. Actual deletion commutes with this restriction on the
target radius-r ball, including the lost-degree deficit. Its finite reference
budget and deleted diameter are derived from ordinary graph geometry.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance singletonBallDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) singletonBallSingletonMemDecidable {A : Type*} (b : A) :
    DecidablePred (fun a => a ∈ ({b} : Set A)) := fun _ => Classical.propDecidable _
local instance (priority := high) canonicalSingletonBallComponentMem
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

variable {V : Type*}

theorem adjacent_ball_subset_succ (G : SimpleGraph V) {b c : V} (hbc : G.Adj b c) (r : ℕ) :
    graphBallVertices G b r ⊆ graphBallVertices G c (r + 1) := by
  intro v hv
  change G.edist c v ≤ ((r + 1 : ℕ) : ℕ∞)
  calc
    _ ≤ G.edist c b + G.edist b v := G.edist_triangle
    _ ≤ 1 + (r : ℕ∞) := add_le_add
      (le_of_eq (SimpleGraph.edist_eq_one_iff_adj.mpr hbc.symm)) hv
    _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; exact add_comm _ _

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

omit [DecidableEq V] in
/-- A connected zero-deficit graph in the base class supplies the actual
reference budget separately on every component. -/
theorem connected_zero_component_budget (g : DeficientGraph V d)
    (hG : g.graph.Connected) (hzero : ∀ v, g.deficit v = 0)
    (hbudget : graphExcess g.graph ≤ finiteOmega d) : g.ComponentReferenceBudget := by
  intro c
  have hzeroC : ∀ v, (g.restrict c.supp).deficit v = 0 := fun v => hzero v.val
  simp only [hzeroC, Finset.sum_const_zero, zero_add]
  exact (connected_induce_graphExcess_le g.graph c.supp hG c.connected_induce_supp).trans hbudget

theorem deleteVertex_distance_bound (g : DeficientGraph V d) (hG : g.graph.Connected)
    (hbudget : graphExcess g.graph ≤ finiteOmega d) (b : V)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R) (i j : {v : V // v ≠ b}) :
    (g.deleteVertex b).graph.dist i j ≤ (finiteOmega d + 1) * (2 * R + 1) := by
  have hS : (g.graph.induce ({b} : Set V)).Connected := by
    apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
    refine ⟨⟨b, rfl⟩, ?_⟩
    intro v
    have hv : v = (⟨b, rfl⟩ : ({b} : Set V)) := Subtype.ext v.property
    subst v
    exact SimpleGraph.Reachable.refl _
  have hh := outside_graph_diameter_bound g.graph hG ({b} : Set V) hS (finiteOmega d)
    hbudget R hR (g.deleteVertexIso b i) (g.deleteVertexIso b j)
  change (g.delete ({b} : Set V)).graph.dist (g.deleteVertexIso b i) (g.deleteVertexIso b j) ≤ _ at hh
  rwa [graphIso_dist (g.deleteVertexIso b)] at hh

/-- Restriction and literal singleton deletion identify the actual target
pair model whenever the ambient target ball is contained in the restriction.
No matrix entry equality is a hypothesis. -/
theorem restrict_deleteVertex_pair_P (g : DeficientGraph V d) (S : Set V)
    (b : S) (i : {v : S // v ≠ b}) (r : ℕ)
    (hi : graphBallVertices g.graph i.val.val r ⊆ S) (q z : ℂ) :
    ((g.restrict S).deleteVertex b).P r z q i i =
      (g.deleteVertex b.val).P r z q
        ⟨i.val.val, fun h => i.property (Subtype.ext h)⟩
        ⟨i.val.val, fun h => i.property (Subtype.ext h)⟩ := by
  let T : Set V := {b.val}
  let Tm : Set S := {b}
  let iset := (g.restrict S).deleteVertexIso b i
  let ii : {v : V // v ≠ b.val} := ⟨i.val.val, fun h => i.property (Subtype.ext h)⟩
  have hTm : ∀ v : S, v ∈ Tm ↔ v.val ∈ T := by
    intro v
    simp only [Tm, T, Set.mem_singleton_iff, Subtype.ext_iff]
  have hTS : T ⊆ S := by
    intro v hv
    have hvb : v = b.val := hv
    simpa only [hvb] using b.property
  let φ := restrictionDeletionGraphIso g.graph S T Tm hTm
  have hball : graphBallVertices (outsideGraph g.graph T) (φ iset).val r ⊆
      {v : (Tᶜ : Set V) | v.val ∈ S} := by
    intro v hv
    exact hi ((graphHom_edist_le
      (SimpleGraph.Embedding.induce (G := g.graph) Tᶜ).toHom (φ iset).val v).trans hv)
  have hleft := ((g.restrict S).delete Tm).P_iso ((g.restrict S).deleteVertex b)
    ((g.restrict S).deleteVertexIso b) ((g.restrict S).deleteVertex_deficit_iso b) r q z i i
  have hmiddle := g.restriction_delete_pair_P S T Tm hTm hTS iset iset r hball hball q z
  have hright := (g.delete T).P_iso (g.deleteVertex b.val) (g.deleteVertexIso b.val)
    (g.deleteVertex_deficit_iso b.val) r q z ii ii
  exact hleft.trans (hmiddle.trans hright.symm)

end DeficientGraph
end LocalLaw
