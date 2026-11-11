import LocalLaw.SingletonBallModel
import LocalLaw.BoundaryNearCounts

/-!
# Source geometry for the singleton observation common ball

The deleted common ball embeds into an actual structural ball of the
original regular graph. Distance from the genuine outer boundary forces
its inherited deficit to vanish. The required margin is explicit: the
common radius r+1 must lie within the structural radius.
-/

noncomputable section
namespace LocalLaw
local instance sourceSingletonGeometryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem outside_ball_excess_le_original_ball (G : SimpleGraph V) (T : Set V)
    (c : (Tᶜ : Set V)) (r R : ℕ) (hmargin : r ≤ R) :
    graphBallExcess (outsideGraph G T) c r ≤ graphBallExcess G c.val R := by
  let f : graphBall (outsideGraph G T) c r →g graphBall G c.val R :=
    { toFun := fun v => ⟨v.val.val, by
        have hh := (graphHom_edist_le
          (SimpleGraph.Embedding.induce (G := G) Tᶜ).toHom c v.val).trans v.property
        exact hh.trans (by exact_mod_cast hmargin)⟩
      map_rel' := fun h => h }
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun v : graphBallVertices G c.val R => v.val) h))
  exact connected_embedding_graphExcess_le _ _
    (graphBall_connected (outsideGraph G T) c r) (graphBall_connected G c.val R) f hf

namespace RegularGraph
variable {N d : ℕ}

/-- The source far-boundary indicator clears every actual lost-degree
deficit in the common radius-(r+1) ball at the second endpoint. -/
theorem singleton_common_ball_zero_deficit (g : RegularGraph N d) (T : Set (Fin N))
    (b c : (Tᶜ : Set (Fin N))) (hbc : (outsideGraph g.graph T).Adj b c) (r : ℕ)
    (hfar : ∀ α : BoundaryOrientedEdge g.graph T,
      ((r + 2 : ℕ) : ℕ∞) < (outsideGraph g.graph T).edist b (boundaryOuterEndpoint g.graph T α))
    (v : (Tᶜ : Set (Fin N)))
    (hv : v ∈ graphBallVertices (outsideGraph g.graph T) c (r + 1)) :
    (g.deficient.delete T).deficit v = 0 := by
  have hdist : (outsideGraph g.graph T).edist b v ≤ ((r + 2 : ℕ) : ℕ∞) := by
    calc
      _ ≤ (outsideGraph g.graph T).edist b c + (outsideGraph g.graph T).edist c v :=
        SimpleGraph.edist_triangle
      _ ≤ 1 + ((r + 1 : ℕ) : ℕ∞) := add_le_add
        (le_of_eq (SimpleGraph.edist_eq_one_iff_adj.mpr hbc)) hv
      _ = _ := by exact_mod_cast (show 1 + (r + 1) = r + 2 by omega)
  letI : IsEmpty {t : T // g.graph.Adj t.val v.val} := ⟨fun t => by
    let α : BoundaryOrientedEdge g.graph T := ⟨(t.val.val, v.val), t.property, t.val.property, v.property⟩
    exact (not_lt_of_ge hdist) (hfar α)⟩
  rw [g.deficient.delete_deficit_eq_removed_neighbors]
  change 0 + Nat.card {t : T // g.graph.Adj t.val v.val} = 0
  simp only [Nat.card_of_isEmpty, Nat.add_zero]

/-- Both source common-model conditions follow from the original structural
ball event and the actual far-boundary indicator. -/
theorem singleton_common_ball_reference_conditions (g : RegularGraph N d) (T : Set (Fin N))
    (b c : (Tᶜ : Set (Fin N))) (hbc : (outsideGraph g.graph T).Adj b c) (r R : ℕ)
    (hmargin : r + 1 ≤ R) (hballs : ∀ v, graphBallExcess g.graph v R ≤ finiteOmega d)
    (hfar : ∀ α : BoundaryOrientedEdge g.graph T,
      ((r + 2 : ℕ) : ℕ∞) < (outsideGraph g.graph T).edist b (boundaryOuterEndpoint g.graph T α)) :
    (∀ v ∈ graphBallVertices (g.deficient.delete T).graph c (r + 1),
      (g.deficient.delete T).deficit v = 0) ∧
    graphBallExcess (g.deficient.delete T).graph c (r + 1) ≤ finiteOmega d := by
  refine ⟨fun v hv => g.singleton_common_ball_zero_deficit T b c hbc r hfar v hv, ?_⟩
  exact (outside_ball_excess_le_original_ball g.graph T c (r + 1) R hmargin).trans (hballs c.val)

end RegularGraph
end LocalLaw
