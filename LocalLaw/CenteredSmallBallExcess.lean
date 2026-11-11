import LocalLaw.ResamplingSmallBallExcess
import LocalLaw.ResamplingBallPreservation
import LocalLaw.BoundaryTreeCounts
import LocalLaw.CoreAttachments

/-!
# Centered small-ball excess transfer and the inverse tree direction

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

local instance centeredSmallBallExcessDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V] {T : Set V} {ι : Type*} [Fintype ι]

theorem fullResample_centered_small_ball_excess (s : LabelledResamplingState V T ι)
    (selector r R ω : ℕ) (hsmall : 2 * r ≤ selector) (o : V) (ell : ℕ)
    (hT : T ⊆ graphBallVertices s.graph o ell) (houter : ell + 2 * r ≤ R)
    (hbudget : graphBallExcess s.graph o R ≤ ω) :
    graphBallExcess (s.fullResample selector).graph o r ≤ ω := by
  let t := s.fullResample selector
  let B := graphBall t.graph o r
  let emb : (graphBallVertices t.graph o r) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hagree : ∀ x y : graphBallVertices t.graph o r,
      x ∉ t.eligibleExteriorInBall selector o r →
      y ∉ t.eligibleExteriorInBall selector o r →
      (t.graph.Adj x.val y.val ↔ s.graph.Adj x.val y.val) :=
    s.fullResample_adj_away_eligibleExterior selector r o
  by_cases hremoved : (t.eligibleExteriorInBall selector o r).Nonempty
  · have hlocal := t.all_even_patterns_support_in_original_core selector r hsmall o
      s.graph o ell hT hremoved hagree
    have hedges : ∀ C : EvenEdgeSubgraph B, C.val.map emb ≤ s.graph :=
      fun C => t.ball_even_pattern_map_old_edges selector r hsmall o s.graph hagree C
    have hsupport : ∀ C : EvenEdgeSubgraph B,
        (C.val.map emb).support ⊆ graphBallVertices s.graph o (ell + 2 * r) := by
      intro C v hv
      obtain ⟨w, hvw⟩ := ((C.val.map emb).mem_support).mp hv
      obtain ⟨a, b, hab, rfl, _⟩ := (SimpleGraph.map_adj emb C.val v w).mp hvw
      exact hlocal C a ((C.val.mem_support).mpr ⟨b, hab⟩)
    have hbound := graphExcess_le_of_even_pattern_localization B s.graph emb
      (graphBallVertices s.graph o (ell + 2 * r)) (graphBall_connected t.graph o r)
      (graphBall_connected s.graph o (ell + 2 * r)) hedges hsupport
    simp only [B, t, graphBall, graphExcess, SimpleGraph.edgeFinset_card,
      ← Nat.card_eq_fintype_card] at hbound
    have hcore : graphBallExcess (s.fullResample selector).graph o r ≤
        graphBallExcess s.graph o (ell + 2 * r) := by
      simp only [graphBallExcess, graphBall, graphExcess, SimpleGraph.edgeFinset_card,
        ← Nat.card_eq_fintype_card]
      exact hbound
    exact hcore.trans ((graphBallExcess_mono_radius s.graph o houter).trans hbudget)
  · have hnot : ∀ x : graphBallVertices t.graph o r,
        x ∉ t.eligibleExteriorInBall selector o r := fun x hx => hremoved ⟨x, hx⟩
    let fOld : B →g s.graph :=
      { toFun := fun v => v.val
        map_rel' := fun {x y} h => (hagree x y (hnot x) (hnot y)).mp h }
    let D := ballHeightParentData t.graph o r
    have hDB : D.tree ≤ B := D.tree_le _ (ballHeightParentData_parent_adj t.graph o r)
    have hmem : ∀ v : graphBallVertices t.graph o r, v.val ∈ graphBallVertices s.graph o r := by
      intro v
      obtain ⟨p, hp⟩ := D.walk_to_root v
      let q := (p.mapLe hDB).map fOld
      have hdist := s.graph.edist_le q.reverse
      apply hdist.trans
      have hheight := ballVertexHeight_le t.graph o r v
      simpa only [q, SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_map,
        SimpleGraph.Walk.mapLe, hp] using ENat.coe_le_coe.mpr hheight
    let fBall : B →g graphBall s.graph o r :=
      { toFun := fun v => ⟨v.val, hmem v⟩
        map_rel' := fun h => fOld.map_rel h }
    have hf : Function.Injective fBall := by
      intro x y h
      exact Subtype.ext (congrArg (fun v : graphBallVertices s.graph o r => v.val) h)
    have hbound := connected_embedding_graphExcess_le B (graphBall s.graph o r)
      (graphBall_connected t.graph o r) (graphBall_connected s.graph o r) fBall hf
    have hfit : r ≤ R := by omega
    simp only [B, t, graphBall, graphExcess, SimpleGraph.edgeFinset_card,
      ← Nat.card_eq_fintype_card] at hbound
    have hcore : graphBallExcess (s.fullResample selector).graph o r ≤
        graphBallExcess s.graph o r := by
      simp only [graphBallExcess, graphBall, graphExcess, SimpleGraph.edgeFinset_card,
        ← Nat.card_eq_fintype_card]
      exact hbound
    exact hcore.trans ((graphBallExcess_mono_radius s.graph o hfit).trans hbudget)

/-- The tree hypothesis belongs to the target graph. Inverting the actual
labelled resampling transfers it to the smaller source ball. -/
theorem fullResample_tree_implies_source_small_tree (s : LabelledResamplingState V T ι)
    (selector r R : ℕ) (hsmall : 2*r≤selector) (o : V) (ell : ℕ)
    (hT : T=graphBallVertices s.graph o ell) (houter : ell+2*r≤R)
    (hTree : (graphBall (s.fullResample selector).graph o R).IsTree) :
    (graphBall s.graph o r).IsTree := by
  let t := s.fullResample selector
  have hnew : graphBallVertices t.graph o ell=T := by
    simpa only [graphSetBall_singleton] using s.fullResample_ball selector {o} ell
      (by simpa only [graphSetBall_singleton] using hT)
  have hTnew : T⊆graphBallVertices t.graph o ell := fun _ hv => hnew.symm ▸ hv
  have hb : graphBallExcess t.graph o R≤0 := (tree_graphExcess_zero _ hTree).le
  have hback := t.fullResample_centered_small_ball_excess selector r R 0 hsmall o ell hTnew houter hb
  have hrestore : (t.fullResample selector).graph=s.graph :=
    congrArg (fun x : LabelledResamplingState V T ι => x.graph) (s.fullResample_twice selector)
  rw [hrestore] at hback
  by_cases hgood : (graphBall s.graph o r).IsTree
  · exact hgood
  · have hpositive := connected_nonTree_excess_positive _ (graphBall_connected s.graph o r) hgood
    exact False.elim ((not_lt_of_ge hback) hpositive)

theorem fullResample_tree_implies_source_eighth_tree (s : LabelledResamplingState V T ι)
    (R : ℕ) (o : V) (ell : ℕ) (hT : T=graphBallVertices s.graph o ell)
    (hmargin : 2*ell+2≤R) (hTree : (graphBall (s.fullResample (R/4)).graph o R).IsTree) :
    (graphBall s.graph o (R/8)).IsTree :=
  s.fullResample_tree_implies_source_small_tree (R/4) (R/8) R (by omega) o ell hT (by omega) hTree

end LabelledResamplingState
end LocalLaw
