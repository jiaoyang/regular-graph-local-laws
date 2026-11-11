import LocalLaw.LocalAdjacentBudget
import LocalLaw.SourceBoundaryGuard

/-! # Base reference budgets for the physical diagonal and edge models

Full regular models have zero deficit. Deleted edge models have zero
inherited deficit only at the actual far-boundary guard. Their connected
pair neighborhood embeds into an original structural ball. Thus the base
reference class, including its diagonal lower bound, is used exactly where
its deficit condition has been proved.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw

local instance localBaseModelBudgetDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*}

theorem pairBall_connected_of_eq_or_adjacent (G : SimpleGraph V) (i j : V) (r : ℕ)
    (hij : i = j ∨ G.Adj i j) : (pairBallGraph G i j r).Connected := by
  rcases hij with rfl | hij
  · have hK : pairBallVertices G i i r = graphBallVertices G i r := by
      ext v
      simp only [pairBallVertices, graphBallVertices, Set.mem_setOf_eq, or_self]
    change (G.induce (pairBallVertices G i i r)).Connected
    rw [hK]
    exact graphBall_connected G i r
  · exact pairBall_connected_of_adjacent G i j r hij

theorem pairBall_subset_succ_of_eq_or_adjacent (G : SimpleGraph V) (i j : V) (r : ℕ)
    (hij : i = j ∨ G.Adj i j) :
    pairBallVertices G i j r ⊆ graphBallVertices G i (r + 1) := by
  rcases hij with rfl | hij
  · intro v hv
    exact hv.elim (fun h => h.trans (ENat.coe_le_coe.mpr (by omega)))
      (fun h => h.trans (ENat.coe_le_coe.mpr (by omega)))
  · exact adjacent_pairBall_subset G i j r hij

namespace RegularGraph
variable {N d : ℕ}

theorem local_pairModel_base_budget (g : RegularGraph N d) (r R : ℕ)
    (hmargin : r + 1 ≤ R) (hballs : ∀ v, graphBallExcess g.graph v R ≤ finiteOmega d)
    (i j : Fin N) (hij : i = j ∨ g.graph.Adj i j) :
    (∑ v, (g.pairModel i j r).deficit v) + graphExcess (g.pairModel i j r).graph ≤ finiteOmega d := by
  have hzero : ∀ v, (g.pairModel i j r).deficit v = 0 := fun _ => rfl
  simp only [hzero, Finset.sum_const_zero, zero_add]
  rcases hij with rfl | hij
  · have hK : pairBallVertices g.graph i i r = graphBallVertices g.graph i r := by
      ext v
      simp only [pairBallVertices, graphBallVertices, Set.mem_setOf_eq, or_self]
    change graphExcess (g.graph.induce (pairBallVertices g.graph i i r)) ≤ finiteOmega d
    rw [hK]
    exact (graphBallExcess_mono_radius g.graph i (by omega : r ≤ R)).trans (hballs i)
  · exact (g.adjacent_pairModel_finiteReferenceBudget r R hmargin hballs i j hij).excess_le

theorem boundaryFarOutside_zero_deficit (g : RegularGraph N d) (T : Set (Fin N)) (h : ℕ)
    (u : (Tᶜ : Set (Fin N))) (hu : u ∈ boundaryFarOutside g.graph T h)
    (v : (Tᶜ : Set (Fin N))) (hv : (outsideGraph g.graph T).edist u v ≤ (h : ℕ∞)) :
    (g.deficient.delete T).deficit v = 0 := by
  letI : IsEmpty {t : T // g.graph.Adj t.val v.val} := ⟨fun t => by
    let α : BoundaryOrientedEdge g.graph T := ⟨(t.val.val, v.val), t.property, t.val.property, v.property⟩
    exact (not_lt_of_ge hv) (hu α)⟩
  rw [g.deficient.delete_deficit_eq_removed_neighbors]
  change 0 + Nat.card {t : T // g.graph.Adj t.val v.val} = 0
  simp only [Nat.card_of_isEmpty, zero_add]

theorem far_deleted_local_pair_base_budget (g : RegularGraph N d) (T : Set (Fin N))
    (r R h : ℕ) (hmargin : r + 1 ≤ R) (hfarMargin : r + 1 ≤ h)
    (hballs : ∀ v, graphBallExcess g.graph v R ≤ finiteOmega d)
    (i j : (Tᶜ : Set (Fin N)))
    (hij : i = j ∨ (outsideGraph g.graph T).Adj i j)
    (hi : i ∈ boundaryFarOutside g.graph T h) :
    let M := (g.deficient.delete T).restrict (pairBallVertices (outsideGraph g.graph T) i j r)
    (∑ v, M.deficit v) + graphExcess M.graph ≤ finiteOmega d := by
  let H := outsideGraph g.graph T
  let K := pairBallVertices H i j r
  let M := (g.deficient.delete T).restrict K
  have hK : (H.induce K).Connected := pairBall_connected_of_eq_or_adjacent H i j r hij
  have hdist (v : K) : H.edist i v.val ≤ ((r + 1 : ℕ) : ℕ∞) :=
    pairBall_subset_succ_of_eq_or_adjacent H i j r hij v.property
  have hzero : ∀ v, M.deficit v = 0 := fun v => g.boundaryFarOutside_zero_deficit T h i hi v.val
    ((hdist v).trans (ENat.coe_le_coe.mpr hfarMargin))
  let f : H.induce K →g graphBall g.graph i.val R :=
    { toFun := fun v => ⟨v.val.val, by
        have hh := (graphHom_edist_le (SimpleGraph.Embedding.induce (G := g.graph) Tᶜ).toHom i v.val).trans (hdist v)
        exact hh.trans (ENat.coe_le_coe.mpr hmargin)⟩
      map_rel' := fun h => h }
  have hf : Function.Injective f := by
    intro v w heq
    have hraw : v.val.val = w.val.val := congrArg
      (fun x : graphBallVertices g.graph i.val R => x.val) heq
    exact Subtype.ext (Subtype.ext hraw)
  have hex := connected_embedding_graphExcess_le (H.induce K) (graphBall g.graph i.val R)
    hK (graphBall_connected g.graph i.val R) f hf
  have hbudget : graphExcess M.graph ≤ finiteOmega d := hex.trans (hballs i.val)
  change (∑ v, M.deficit v) + graphExcess M.graph ≤ finiteOmega d
  simpa only [hzero, Finset.sum_const_zero, zero_add] using hbudget

end RegularGraph
end LocalLaw
