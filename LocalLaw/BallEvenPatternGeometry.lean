import LocalLaw.EvenCycleSpaceExact
import LocalLaw.ResamplingEvenPatternExclusion

/-!
# The whole cyclic part of a small ball avoids accepted triples

The actual shortest-distance parent tree supplies fundamental cycles with
at most 2r+1 supported vertices. Local I/J geometry excludes each generator
from every accepted triple. Finite cycle-code generation then excludes every
even edge pattern in the ball, even when that pattern has many vertices.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw

local instance ballEvenPatternDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V W : Type*} [Fintype V] [Fintype W]

theorem mapped_even_pattern (F : SimpleGraph V) (f : V ↪ W)
    (heven : ∀ v, Even (F.degree v)) : ∀ w, Even ((F.map f).degree w) := by
  intro w
  by_cases hw : w ∈ Set.range f
  · obtain ⟨v, rfl⟩ := hw
    have h := mappedPattern_degree_image F f v
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h ⊢
    rw [h]
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heven v
  · have h := mappedPattern_degree_outside F f w hw
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h ⊢
    rw [h]
    exact Even.zero

theorem mapped_pattern_support_card_le (F : SimpleGraph V) (f : V ↪ W) :
    (F.map f).support.toFinset.card ≤ F.support.toFinset.card := by
  have hsub : (F.map f).support.toFinset ⊆ F.support.toFinset.image f := by
    intro w hw
    obtain ⟨z, hwz⟩ := ((F.map f).mem_support).mp (Set.mem_toFinset.mp hw)
    obtain ⟨v, u, hvu, hv, _⟩ := (SimpleGraph.map_adj f F w z).mp hwz
    exact Finset.mem_image.mpr ⟨v, Set.mem_toFinset.mpr ((F.mem_support).mpr ⟨u, hvu⟩), hv⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

omit [Fintype V] [Fintype W] in
theorem mapped_pattern_mem_support (F : SimpleGraph V) (f : V ↪ W)
    {v : V} (hv : v ∈ F.support) : f v ∈ (F.map f).support := by
  obtain ⟨u, hvu⟩ := (F.mem_support).mp hv
  exact ((F.map f).mem_support).mpr ⟨f u, SimpleGraph.map_adj_apply.mpr hvu⟩

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*}

theorem eligible_even_pattern_avoids_exterior (s : LabelledResamplingState V T ι)
    (radius : ℕ) (i : ι) (hi : s.Eligible radius i) (F : SimpleGraph V) (hFG : F ≤ s.graph)
    (heven : ∀ v, Even (F.degree v)) (hsize : F.support.toFinset.card ≤ radius + 1) :
    ∀ x ∈ (s.quad i).exterior, x ∉ F.support := by
  intro x hx
  have hout : x ∉ T := fun ht => Set.disjoint_left.mp
    (sampledSwitching_exterior_disjoint s.graph T s.samples (s.boundary i)) hx ht
  exact s.eligible_even_pattern_avoids_triple radius i hi F hFG heven hsize ⟨x, hout⟩ hx

/-- Every even edge pattern in an actual radius-r ball avoids an accepted
triple, without any bound on the total support of the even pattern itself. -/
theorem ball_even_patterns_avoid_exterior (s : LabelledResamplingState V T ι)
    (radius r : ℕ) (hsmall : 2 * r ≤ radius) (i : ι) (hi : s.Eligible radius i)
    (o : V) (C : EvenEdgeSubgraph (graphBall s.graph o r)) :
    ∀ v : graphBallVertices s.graph o r, v.val ∈ (s.quad i).exterior → v ∉ C.val.support := by
  let B := graphBall s.graph o r
  let D := ballHeightParentData s.graph o r
  have hDB : D.tree ≤ B := D.tree_le B (ballHeightParentData_parent_adj s.graph o r)
  let A : Set (graphBallVertices s.graph o r) := {v | v.val ∈ (s.quad i).exterior}
  have hgenerators : ∀ e : (B \ D.tree).edgeSet, ∃ F : EvenEdgeSubgraph B,
      evenSubgraphCode B D.tree F = {e} ∧ ∀ v ∈ A, v ∉ F.val.support := by
    rintro ⟨z, hz⟩
    induction z using Sym2.inductionOn with
    | _ a b =>
      change B.Adj a b ∧ ¬D.tree.Adj a b at hz
      obtain ⟨pa, hpa⟩ := D.walk_to_root b
      obtain ⟨pb, hpb⟩ := D.walk_to_root a
      let p₀ := pa.append pb.reverse
      let p := p₀.bypass
      have hp : p.IsPath := p₀.bypass_isPath
      have hpLen : p.length ≤ 2 * r := by
        have hlen : p₀.length ≤ 2 * r := by
          simp only [p₀, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hpa, hpb]
          have ha := ballVertexHeight_le s.graph o r a
          have hb := ballVertexHeight_le s.graph o r b
          change D.height a ≤ r at ha
          change D.height b ≤ r at hb
          omega
        exact p₀.length_bypass_le.trans hlen
      obtain ⟨F, _, _, hFsize, hcode⟩ := fundamental_even_cycle_of_path B D.tree hDB hz.1 hz.2 p hp
      refine ⟨F, hcode, ?_⟩
      let emb : (graphBallVertices s.graph o r) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
      have hmap : F.val.map emb ≤ s.graph := by
        rw [SimpleGraph.map_le_iff_le_comap]
        intro a b hab
        exact F.property.1 hab
      have hmapEven := mapped_even_pattern F.val emb F.property.2
      have hmapSize : (F.val.map emb).support.toFinset.card ≤ radius + 1 :=
        (mapped_pattern_support_card_le F.val emb).trans (by omega)
      have hEvenCanonical : ∀ v, Even (Nat.card ((F.val.map emb).neighborSet v)) := by
        simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hmapEven
      have hSizeCanonical : Nat.card (F.val.map emb).support ≤ radius + 1 := by
        simpa only [Set.toFinset_card, ← Nat.card_eq_fintype_card] using hmapSize
      have havoid := s.eligible_even_pattern_avoids_exterior radius i hi (F.val.map emb) hmap
        (fun v => by
          simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hEvenCanonical v)
        (by simpa only [Set.toFinset_card, ← Nat.card_eq_fintype_card] using hSizeCanonical)
      intro v hv hsupport
      exact havoid v.val hv (mapped_pattern_mem_support F.val emb hsupport)
  let gen : (B \ D.tree).edgeSet → EvenEdgeSubgraph B := fun e => Classical.choose (hgenerators e)
  have hcode : ∀ e, evenSubgraphCode B D.tree (gen e) = {e} :=
    fun e => (Classical.choose_spec (hgenerators e)).1
  have havoid : ∀ e, ∀ v ∈ A, v ∉ (gen e).val.support :=
    fun e => (Classical.choose_spec (hgenerators e)).2
  exact even_subgraphs_avoid_of_generators B D.tree D.tree_isTree.IsAcyclic A gen hcode havoid C

end LabelledResamplingState
end LocalLaw
