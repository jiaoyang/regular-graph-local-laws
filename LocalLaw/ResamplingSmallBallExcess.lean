import LocalLaw.ResamplingSmallCyclicCore
import LocalLaw.EvenPatternTransfer

/-!
# Actual small-ball excess stability under the full local resampling

If a switched ball meets an eligible exterior vertex, its entire even-pattern
space localizes in the original interior core ball. Otherwise all of its
edges and parent paths are unchanged. The actual injective cycle-space map
therefore preserves the original excess budget. This proves the radius-R/8
part of Proposition 5.12 without assuming the switched excess conclusion.
-/

noncomputable section
set_option maxHeartbeats 2000000
namespace LocalLaw
namespace LabelledResamplingState

local instance resamplingSmallBallExcessDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V] {T : Set V} {ι : Type*} [Fintype ι]

theorem fullResample_small_ball_excess (s : LabelledResamplingState V T ι)
    (selector r R ω : ℕ) (hsmall : 2 * r ≤ selector) (o : V) (ell : ℕ)
    (hT : T ⊆ graphBallVertices s.graph o ell) (houter : ell + 2 * r ≤ R)
    (hbudget : ∀ v, graphBallExcess s.graph v R ≤ ω) (center : V) :
    graphBallExcess (s.fullResample selector).graph center r ≤ ω := by
  let t := s.fullResample selector
  let B := graphBall t.graph center r
  let emb : (graphBallVertices t.graph center r) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hagree : ∀ x y : graphBallVertices t.graph center r,
      x ∉ t.eligibleExteriorInBall selector center r →
      y ∉ t.eligibleExteriorInBall selector center r →
      (t.graph.Adj x.val y.val ↔ s.graph.Adj x.val y.val) :=
    s.fullResample_adj_away_eligibleExterior selector r center
  by_cases hremoved : (t.eligibleExteriorInBall selector center r).Nonempty
  · have hlocal := t.all_even_patterns_support_in_original_core selector r hsmall center
      s.graph o ell hT hremoved hagree
    have hedges : ∀ C : EvenEdgeSubgraph B, C.val.map emb ≤ s.graph :=
      fun C => t.ball_even_pattern_map_old_edges selector r hsmall center s.graph hagree C
    have hsupport : ∀ C : EvenEdgeSubgraph B,
        (C.val.map emb).support ⊆ graphBallVertices s.graph o (ell + 2 * r) := by
      intro C v hv
      obtain ⟨w, hvw⟩ := ((C.val.map emb).mem_support).mp hv
      obtain ⟨a, b, hab, rfl, _⟩ := (SimpleGraph.map_adj emb C.val v w).mp hvw
      exact hlocal C a ((C.val.mem_support).mpr ⟨b, hab⟩)
    have hbound := graphExcess_le_of_even_pattern_localization B s.graph emb
      (graphBallVertices s.graph o (ell + 2 * r)) (graphBall_connected t.graph center r)
      (graphBall_connected s.graph o (ell + 2 * r)) hedges hsupport
    simp only [B, t, graphBall, graphExcess, SimpleGraph.edgeFinset_card,
      ← Nat.card_eq_fintype_card] at hbound
    have hcore : graphBallExcess (s.fullResample selector).graph center r ≤
        graphBallExcess s.graph o (ell + 2 * r) := by
      simp only [graphBallExcess, graphBall, graphExcess, SimpleGraph.edgeFinset_card,
        ← Nat.card_eq_fintype_card]
      exact hbound
    exact hcore.trans ((graphBallExcess_mono_radius s.graph o houter).trans (hbudget o))
  · have hnot : ∀ x : graphBallVertices t.graph center r,
        x ∉ t.eligibleExteriorInBall selector center r := fun x hx => hremoved ⟨x, hx⟩
    let fOld : B →g s.graph :=
      { toFun := fun v => v.val
        map_rel' := fun {x y} h => (hagree x y (hnot x) (hnot y)).mp h }
    let D := ballHeightParentData t.graph center r
    have hDB : D.tree ≤ B := D.tree_le _ (ballHeightParentData_parent_adj t.graph center r)
    have hmem : ∀ v : graphBallVertices t.graph center r, v.val ∈ graphBallVertices s.graph center r := by
      intro v
      obtain ⟨p, hp⟩ := D.walk_to_root v
      let q := (p.mapLe hDB).map fOld
      have hdist := s.graph.edist_le q.reverse
      apply hdist.trans
      have hheight := ballVertexHeight_le t.graph center r v
      simpa only [q, SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_map,
        SimpleGraph.Walk.mapLe, hp] using ENat.coe_le_coe.mpr hheight
    let fBall : B →g graphBall s.graph center r :=
      { toFun := fun v => ⟨v.val, hmem v⟩
        map_rel' := fun h => fOld.map_rel h }
    have hf : Function.Injective fBall := by
      intro x y h
      exact Subtype.ext (congrArg (fun v : graphBallVertices s.graph center r => v.val) h)
    have hbound := connected_embedding_graphExcess_le B (graphBall s.graph center r)
      (graphBall_connected t.graph center r) (graphBall_connected s.graph center r) fBall hf
    have hfit : r ≤ R := by omega
    simp only [B, t, graphBall, graphExcess, SimpleGraph.edgeFinset_card,
      ← Nat.card_eq_fintype_card] at hbound
    have hcore : graphBallExcess (s.fullResample selector).graph center r ≤
        graphBallExcess s.graph center r := by
      simp only [graphBallExcess, graphBall, graphExcess, SimpleGraph.edgeFinset_card,
        ← Nat.card_eq_fintype_card]
      exact hbound
    exact hcore.trans ((graphBallExcess_mono_radius s.graph center hfit).trans (hbudget center))

/-- Source radius-R/8 stability, with literal rounded integer radii. -/
theorem fullResample_radius_eighth_excess (s : LabelledResamplingState V T ι)
    (R ω : ℕ) (o : V) (ell : ℕ) (hT : T ⊆ graphBallVertices s.graph o ell)
    (hmargin : 2 * ell + 2 ≤ R) (hbudget : ∀ v, graphBallExcess s.graph v R ≤ ω) :
    ∀ center, graphBallExcess (s.fullResample (R / 4)).graph center (R / 8) ≤ ω := by
  apply s.fullResample_small_ball_excess (R / 4) (R / 8) R ω (by omega) o ell hT
    (by omega) hbudget

end LabelledResamplingState
end LocalLaw
