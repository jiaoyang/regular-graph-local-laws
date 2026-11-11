import LocalLaw.DeletedDiagonalReference
import LocalLaw.SingletonBallModel

/-!
# Actual finite reference budgets for adjacent pair models

Adjacent endpoint r-balls lie in a common (r+1)-ball. Their genuine connected
restriction inherits the base or positive-deficit finite class. For deletion
of the actual root ball, the near/far cut argument is already supplied by the
proved diagonal common-ball budget.
-/

noncomputable section
namespace LocalLaw
local instance localAdjacentBudgetDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

omit [DecidableEq V] in
theorem nested_connected_restriction_budget (g : DeficientGraph V d) (S K : Set V)
    (hKS : K ⊆ S) (hS : (g.graph.induce S).Connected) (hK : (g.graph.induce K).Connected)
    (hbudget : (g.restrict S).FiniteReferenceBudget) : (g.restrict K).FiniteReferenceBudget := by
  let Km : Set S := {v | v.val ∈ K}
  let e : ((g.restrict S).graph.induce Km) ≃g g.graph.induce K :=
    { toEquiv :=
        { toFun := fun v => ⟨v.val.val, v.property⟩
          invFun := fun v => ⟨⟨v.val, hKS v.property⟩, v.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      map_rel_iff' := Iff.rfl }
  have hKm : ((g.restrict S).graph.induce Km).Connected := e.connected_iff.mpr hK
  have hsmall := (g.restrict S).restrict_finiteReferenceBudget Km hS hKm hbudget
  exact ((g.restrict S).restrict Km).finiteReferenceBudget_of_iso (g.restrict K) e.symm (fun _ => rfl) hsmall

end DeficientGraph

section Adjacent
variable {V : Type*}

theorem pairBall_connected_of_adjacent (G : SimpleGraph V) (u v : V) (r : ℕ) (huv : G.Adj u v) :
    (pairBallGraph G u v r).Connected :=
  pairBall_connected_of_reachable_endpoints G u v r
    (show (pairBallGraph G u v r).Adj (pairBallLeft G u v r) (pairBallRight G u v r) from huv).reachable

theorem adjacent_pairBall_subset (G : SimpleGraph V) (u v : V) (r : ℕ) (huv : G.Adj u v) :
    pairBallVertices G u v r ⊆ graphBallVertices G u (r + 1) := by
  intro w hw
  rcases hw with hw | hw
  · exact hw.trans (ENat.coe_le_coe.mpr (by omega))
  · exact adjacent_ball_subset_succ G huv.symm r hw

end Adjacent

namespace RegularGraph
variable {N d : ℕ}

theorem adjacent_pairModel_finiteReferenceBudget (g : RegularGraph N d) (r R : ℕ)
    (hmargin : r + 1 ≤ R) (hballs : ∀ v, graphBallExcess g.graph v R ≤ finiteOmega d)
    (u v : Fin N) (huv : g.graph.Adj u v) : (g.pairModel u v r).FiniteReferenceBudget := by
  let S := graphBallVertices g.graph u (r + 1)
  have hzero : ∀ x : S, (g.deficient.restrict S).deficit x = 0 := fun _ => rfl
  have hS : (g.deficient.restrict S).FiniteReferenceBudget := by
    left
    simp only [hzero, Finset.sum_const_zero, zero_add]
    exact (graphBallExcess_mono_radius g.graph u hmargin).trans (hballs u)
  exact g.deficient.nested_connected_restriction_budget S (pairBallVertices g.graph u v r)
    (adjacent_pairBall_subset g.graph u v r huv) (graphBall_connected g.graph u (r + 1))
    (pairBall_connected_of_adjacent g.graph u v r huv) hS

/-- A deleted adjacent pair has an actual allowed finite reference budget.
Its only structural input is the original small-ball excess bound. -/
theorem deleted_adjacent_pair_finiteReferenceBudget (g : RegularGraph N d) (o : Fin N)
    (ell r R : ℕ) (hmargin : r + 2 * ell + 2 ≤ R)
    (hballs : ∀ v, graphBallExcess g.graph v R ≤ finiteOmega d)
    (u v : ((graphBallVertices g.graph o ell)ᶜ : Set (Fin N)))
    (huv : (outsideGraph g.graph (graphBallVertices g.graph o ell)).Adj u v) :
    ((g.deficient.delete (graphBallVertices g.graph o ell)).restrict
      (pairBallVertices (outsideGraph g.graph (graphBallVertices g.graph o ell)) u v r)).FiniteReferenceBudget := by
  let T := graphBallVertices g.graph o ell
  let H := outsideGraph g.graph T
  let S := pairBallVertices H u u (r + 1)
  have hS : ((g.deficient.delete T).restrict S).FiniteReferenceBudget :=
    g.deleted_diagonal_finiteReferenceBudget o ell (r + 1) R (by omega) hballs u
  have hsubset : pairBallVertices H u v r ⊆ S := by
    intro w hw
    exact Or.inl (adjacent_pairBall_subset H u v r huv hw)
  exact (g.deficient.delete T).nested_connected_restriction_budget S (pairBallVertices H u v r)
    hsubset (g.deletedDiagonalModel_connected T (r + 1) u)
    (pairBall_connected_of_adjacent H u v r huv) hS

end RegularGraph
end LocalLaw
