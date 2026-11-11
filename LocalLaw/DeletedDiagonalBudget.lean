import LocalLaw.DeletedRestrictionBudget
import LocalLaw.SampleTreeNeighborhood

/-! # Actual finite reference budgets for deleted diagonal local models

If the local deleted ball touches a removed neighbor, the whole connected
removed ball fits in one original ball of radius r+2ell+1. Deletion in that
common zero-deficit finite model and genuine restriction give the extended
class. Otherwise the local inherited deficit vanishes and original ball
excess directly bounds its connected restriction.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw

local instance deletedDiagonalBudgetDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace RegularGraph
variable {N d : ℕ}

theorem deleted_diagonal_finiteReferenceBudget (g : RegularGraph N d) (o : Fin N)
    (ell r R : ℕ) (hmargin : r + 2 * ell + 1 ≤ R)
    (hballs : ∀ v, graphBallExcess g.graph v R ≤ finiteOmega d)
    (u : ((graphBallVertices g.graph o ell)ᶜ : Set (Fin N))) :
    ((g.deficient.delete (graphBallVertices g.graph o ell)).restrict
      (pairBallVertices (outsideGraph g.graph (graphBallVertices g.graph o ell)) u u r)).FiniteReferenceBudget := by
  classical
  let T := graphBallVertices g.graph o ell
  let H := outsideGraph g.graph T
  let K := pairBallVertices H u u r
  have hKball : K = graphBallVertices H u r := by
    ext v
    simp only [K, pairBallVertices, graphBallVertices, Set.mem_setOf_eq, or_self]
  have hK : ((g.deficient.delete T).graph.induce K).Connected := by
    change (H.induce K).Connected
    rw [hKball]
    exact graphBall_connected H u r
  have hOld : ∀ v ∈ K, g.graph.edist u.val v.val ≤ (r : ℕ∞) := by
    intro v hv
    let f : H →g g.graph := { toFun := Subtype.val, map_rel' := fun h => h }
    apply (graphHom_edist_le f u v).trans
    rw [hKball] at hv
    exact hv
  by_cases htouch : ∃ v ∈ K, ∃ t ∈ T, g.graph.Adj v.val t
  · obtain ⟨v, hv, t, ht, hvt⟩ := htouch
    let M := graphBallVertices g.graph u.val (r + 2 * ell + 1)
    have hTM : T ⊆ M := by
      intro t' ht'
      have hTT : g.graph.edist t t' ≤ ((ell + ell : ℕ) : ℕ∞) := by
        apply (SimpleGraph.edist_triangle (G := g.graph) (u := t) (v := o) (w := t')).trans
        have htO : g.graph.edist t o ≤ (ell : ℕ∞) := by
          simpa only [SimpleGraph.edist_comm] using ht
        exact (add_le_add htO ht').trans_eq (by simp only [Nat.cast_add])
      have hvT : g.graph.edist v.val t' ≤ (1 : ℕ∞) + ((ell + ell : ℕ) : ℕ∞) :=
        (SimpleGraph.edist_triangle (G := g.graph) (u := v.val) (v := t) (w := t')).trans
          (add_le_add (by simpa using SimpleGraph.edist_le hvt.toWalk) hTT)
      change g.graph.edist u.val t' ≤ ((r + 2 * ell + 1 : ℕ) : ℕ∞)
      apply ((SimpleGraph.edist_triangle (G := g.graph) (u := u.val) (v := v.val) (w := t')).trans
        (add_le_add (hOld v hv) hvT)).trans_eq
      push_cast
      ring
    have hKM : ∀ v ∈ K, v.val ∈ M := by
      intro v hv
      exact (hOld v hv).trans (ENat.coe_le_coe.mpr (by omega))
    have hMbudget : graphExcess (g.graph.induce M) ≤ finiteOmega d := by
      have hh := (graphBallExcess_mono_radius g.graph u.val hmargin).trans (hballs u.val)
      exact hh
    exact g.deficient.deleted_connected_restriction_finiteReferenceBudget M T (fun _ => rfl)
      (graphBall_connected g.graph u.val _) (graphBall_connected g.graph o ell) hTM hMbudget K hK hKM
  · have hzero : ∀ v : K, ((g.deficient.delete T).restrict K).deficit v = 0 := by
      intro v
      change (g.deficient.delete T).deficit v.val = 0
      rw [g.deficient.delete_deficit_eq_removed_neighbors]
      haveI : IsEmpty {t : T // g.graph.Adj t.val v.val.val} := ⟨by
        intro t
        exact htouch ⟨v.val, v.property, t.val.val, t.val.property, t.property.symm⟩⟩
      change 0 + Nat.card {t : T // g.graph.Adj t.val v.val.val} = 0
      simp only [Nat.card_of_isEmpty, zero_add]
    let f : ((g.deficient.delete T).graph.induce K) →g graphBall g.graph u.val r :=
      { toFun := fun v => ⟨v.val.val, hOld v.val v.property⟩
        map_rel' := fun h => h }
    have hf : Function.Injective f := by
      intro v w h
      have hraw : v.val.val = w.val.val := congrArg
        (fun y : graphBallVertices g.graph u.val r => y.val) h
      exact Subtype.ext (Subtype.ext hraw)
    have hex := connected_embedding_graphExcess_le ((g.deficient.delete T).graph.induce K)
      (graphBall g.graph u.val r) hK (graphBall_connected g.graph u.val r) f hf
    have hbase : graphExcess (graphBall g.graph u.val r) ≤ finiteOmega d :=
      (graphBallExcess_mono_radius g.graph u.val (by omega : r ≤ R)).trans (hballs u.val)
    left
    change (∑ v : K, ((g.deficient.delete T).restrict K).deficit v) +
      graphExcess ((g.deficient.delete T).graph.induce K) ≤ finiteOmega d
    simp only [hzero, Finset.sum_const_zero, zero_add]
    exact hex.trans hbase

end RegularGraph
end LocalLaw
