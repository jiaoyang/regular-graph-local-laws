import LocalLaw.BallEvenPatternGeometry

/-!
# Lift short-pattern avoidance to every even pattern in an actual ball

Actual BFS fundamental cycles have support size at most 2r+1. If all such
small ambient even patterns avoid A, every even pattern in the radius-r ball
avoids A by the proved finite cycle-code generation theorem.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw

local instance ballEvenGeneratorAvoidanceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V]

theorem ball_even_patterns_avoid_of_small_patterns (H : SimpleGraph V) (o : V) (r : ℕ)
    (A : Set V)
    (hsmall : ∀ F : SimpleGraph V, F ≤ H → (∀ v, Even (F.degree v)) →
      F.support.toFinset.card ≤ 2 * r + 1 → ∀ x ∈ A, x ∉ F.support)
    (C : EvenEdgeSubgraph (graphBall H o r)) :
    ∀ v : graphBallVertices H o r, v.val ∈ A → v ∉ C.val.support := by
  let B := graphBall H o r
  let D := ballHeightParentData H o r
  let A' : Set (graphBallVertices H o r) := {v | v.val ∈ A}
  have hDB : D.tree ≤ B := D.tree_le _ (ballHeightParentData_parent_adj H o r)
  have hgens : ∀ e : (B \ D.tree).edgeSet, ∃ F : EvenEdgeSubgraph B,
      evenSubgraphCode B D.tree F = {e} ∧ ∀ v ∈ A', v ∉ F.val.support := by
    rintro ⟨z, hz⟩
    induction z using Sym2.inductionOn with
    | _ a b =>
      change B.Adj a b ∧ ¬D.tree.Adj a b at hz
      obtain ⟨pa, hpa⟩ := D.walk_to_root b
      obtain ⟨pb, hpb⟩ := D.walk_to_root a
      let p₀ := pa.append pb.reverse
      let p := p₀.bypass
      have hp : p.IsPath := p₀.bypass_isPath
      have hlen : p.length ≤ 2 * r := by
        have hlen₀ : p₀.length ≤ 2 * r := by
          simp only [p₀, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hpa, hpb]
          have ha := ballVertexHeight_le H o r a
          have hb := ballVertexHeight_le H o r b
          change D.height a ≤ r at ha
          change D.height b ≤ r at hb
          omega
        exact p₀.length_bypass_le.trans hlen₀
      obtain ⟨F, _, _, hFsize, hcode⟩ := fundamental_even_cycle_of_path B D.tree hDB hz.1 hz.2 p hp
      refine ⟨F, hcode, ?_⟩
      let emb : (graphBallVertices H o r) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
      have hmap : F.val.map emb ≤ H := by
        rw [SimpleGraph.map_le_iff_le_comap]
        exact fun _ _ h => F.property.1 h
      have hEvenCanonical : ∀ v, Even (Nat.card ((F.val.map emb).neighborSet v)) := by
        simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using
          mapped_even_pattern F.val emb F.property.2
      have hSize : Nat.card (F.val.map emb).support ≤ 2 * r + 1 := by
        have h := (mapped_pattern_support_card_le F.val emb).trans (by omega : F.val.support.toFinset.card ≤ 2 * r + 1)
        simpa only [Set.toFinset_card, ← Nat.card_eq_fintype_card] using h
      have havoid := hsmall (F.val.map emb) hmap
        (fun v => by
          simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hEvenCanonical v)
        (by simpa only [Set.toFinset_card, ← Nat.card_eq_fintype_card] using hSize)
      intro v hv hs
      exact havoid v.val hv (mapped_pattern_mem_support F.val emb hs)
  let gen : (B \ D.tree).edgeSet → EvenEdgeSubgraph B := fun e => Classical.choose (hgens e)
  have hcode : ∀ e, evenSubgraphCode B D.tree (gen e) = {e} :=
    fun e => (Classical.choose_spec (hgens e)).1
  have havoid : ∀ e, ∀ v ∈ A', v ∉ (gen e).val.support :=
    fun e => (Classical.choose_spec (hgens e)).2
  exact even_subgraphs_avoid_of_generators B D.tree D.tree_isTree.IsAcyclic A' gen hcode havoid C

end LocalLaw
