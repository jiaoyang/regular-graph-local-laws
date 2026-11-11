import LocalLaw.ResamplingCoreLocalization
import LocalLaw.ResamplingEdgeAgreement

/-!
# The whole cyclic core lies in the original interior neighborhood

Every actual fundamental generator has connected parent-tree support. The
crossing-T component lemma localizes each generator, and finite cycle-code
assembly localizes every even pattern, with no support-size hypothesis on
that pattern. Old-edge agreement is a pointwise hypothesis in the generic
lemma and is supplied by the actual full-resampling theorem when applied.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
namespace LabelledResamplingState

local instance resamplingSmallCoreDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V] {T : Set V} {ι : Type*}

theorem ball_even_pattern_avoids_eligibleExterior (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (hsmall : 2 * r ≤ selector) (center : V)
    (C : EvenEdgeSubgraph (graphBall s.graph center r)) :
    ∀ x ∈ C.val.support, x ∉ s.eligibleExteriorInBall selector center r := by
  intro x hx hA
  obtain ⟨i, hi, hext⟩ := hA
  exact s.ball_even_patterns_avoid_exterior selector r hsmall i hi center C x hext hx

theorem all_even_patterns_support_in_original_core (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (hsmall : 2 * r ≤ selector) (center : V)
    (G : SimpleGraph V) (o : V) (ell : ℕ) (hT : T ⊆ graphBallVertices G o ell)
    (hremoved : (s.eligibleExteriorInBall selector center r).Nonempty)
    (hagree : ∀ x y : graphBallVertices s.graph center r,
      x ∉ s.eligibleExteriorInBall selector center r →
      y ∉ s.eligibleExteriorInBall selector center r →
      (s.graph.Adj x.val y.val ↔ G.Adj x.val y.val))
    (C : EvenEdgeSubgraph (graphBall s.graph center r)) :
    ∀ x ∈ C.val.support, x.val ∈ graphBallVertices G o (ell + 2 * r) := by
  let B := graphBall s.graph center r
  let D := ballHeightParentData s.graph center r
  let OutsideCore : Set (graphBallVertices s.graph center r) :=
    {x | x.val ∉ graphBallVertices G o (ell + 2 * r)}
  have hDB : D.tree ≤ B := D.tree_le _ (ballHeightParentData_parent_adj s.graph center r)
  have hgens : ∀ e : (B \ D.tree).edgeSet, ∃ F : EvenEdgeSubgraph B,
      evenSubgraphCode B D.tree F = {e} ∧ ∀ x ∈ OutsideCore, x ∉ F.val.support := by
    rintro ⟨z, hz⟩
    induction z using Sym2.inductionOn with
    | _ a b =>
      change B.Adj a b ∧ ¬D.tree.Adj a b at hz
      obtain ⟨p, hp⟩ := D.tree_isTree.isConnected.exists_isPath b a
      obtain ⟨F, hcode, _, hconn⟩ :=
        fundamental_even_cycle_with_connected_tree_support B D.tree hDB hz.1 hz.2 p hp
      have hne : F.val ≠ ⊥ := by
        intro hbot
        have he : (⟨s(a, b), hz.1, hz.2⟩ : (B \ D.tree).edgeSet) ∈ evenSubgraphCode B D.tree F := by
          rw [hcode]
          exact Set.mem_singleton _
        change s(a, b) ∈ F.val.edgeSet at he
        simp only [hbot, SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false] at he
      have hlocal := s.even_generator_support_in_original_core selector r hsmall center G o ell hT
        hremoved hagree F hconn (s.ball_even_pattern_avoids_eligibleExterior selector r hsmall center F) hne
      refine ⟨F, hcode, ?_⟩
      intro x hx hsupport
      exact hx (hlocal x hsupport)
  let gen : (B \ D.tree).edgeSet → EvenEdgeSubgraph B := fun e => Classical.choose (hgens e)
  have hcode : ∀ e, evenSubgraphCode B D.tree (gen e) = {e} :=
    fun e => (Classical.choose_spec (hgens e)).1
  have havoid : ∀ e, ∀ x ∈ OutsideCore, x ∉ (gen e).val.support :=
    fun e => (Classical.choose_spec (hgens e)).2
  have h := even_subgraphs_avoid_of_generators B D.tree D.tree_isTree.IsAcyclic OutsideCore gen hcode havoid C
  intro x hx
  by_contra hnot
  exact h x hnot hx

/-- Mapping a small-ball even pattern to ambient vertices produces only
original edges. This uses actual even-pattern avoidance, not an assumed
edge-by-edge conclusion of geometric resampling stability. -/
theorem ball_even_pattern_map_old_edges (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (hsmall : 2 * r ≤ selector) (center : V) (G : SimpleGraph V)
    (hagree : ∀ x y : graphBallVertices s.graph center r,
      x ∉ s.eligibleExteriorInBall selector center r →
      y ∉ s.eligibleExteriorInBall selector center r →
      (s.graph.Adj x.val y.val ↔ G.Adj x.val y.val))
    (C : EvenEdgeSubgraph (graphBall s.graph center r)) :
    C.val.map (⟨Subtype.val, Subtype.val_injective⟩ : (graphBallVertices s.graph center r) ↪ V) ≤ G := by
  let emb : (graphBallVertices s.graph center r) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  intro x y hxy
  obtain ⟨a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj emb C.val x y).mp hxy
  have havoid := s.ball_even_pattern_avoids_eligibleExterior selector r hsmall center C
  exact (hagree a b (havoid a ((C.val.mem_support).mpr ⟨b, hab⟩))
    (havoid b ((C.val.mem_support).mpr ⟨a, hab.symm⟩))).mp (C.property.1 hab)

end LabelledResamplingState
end LocalLaw
