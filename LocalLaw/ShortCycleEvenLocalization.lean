import LocalLaw.BallEvenGeneratorAvoidance

/-!
# Localizing every ball-even pattern from its short actual cycles

The shortest-distance parent tree gives explicit fundamental cycles of length
at most 2r+1. Their literal cycle support is localized by the hypothesis.
Actual finite XOR generation then localizes every even edge pattern in the
ball, without a bound on that pattern's total support.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance shortCycleEvenLocalizationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V]

theorem ball_even_pattern_support_of_short_cycles (H : SimpleGraph V) (o : V) (r : ℕ) (S : Set V)
    (hcycles : ∀ v : graphBallVertices H o r, ∀ p : (graphBall H o r).Walk v v,
      p.IsCycle → p.length ≤ 2 * r + 1 → ∀ w ∈ p.support, w.val ∈ S)
    (C : EvenEdgeSubgraph (graphBall H o r)) :
    ∀ v ∈ C.val.support, v.val ∈ S := by
  let B := graphBall H o r
  let D := ballHeightParentData H o r
  let A : Set (graphBallVertices H o r) := {v | v.val ∉ S}
  have hDB : D.tree ≤ B := D.tree_le _ (ballHeightParentData_parent_adj H o r)
  have hgens : ∀ e : (B \ D.tree).edgeSet, ∃ F : EvenEdgeSubgraph B,
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
      have hlen : p.length ≤ 2 * r := by
        apply p₀.length_bypass_le.trans
        simp only [p₀, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hpa, hpb]
        have ha := ballVertexHeight_le H o r a
        have hb := ballVertexHeight_le H o r b
        change D.height a ≤ r at ha
        change D.height b ≤ r at hb
        omega
      let pB := p.mapLe hDB
      have hpB : pB.IsPath := hp.mapLe hDB
      have hnot : s(a, b) ∉ pB.edges := by
        intro he
        have he' : s(a, b) ∈ p.edges := by
          simpa only [pB, SimpleGraph.Walk.mapLe, SimpleGraph.Walk.edges_map,
            SimpleGraph.Hom.coe_ofLE, Sym2.map_id, List.map_id] using he
        exact hz.2 (p.adj_of_mem_edges he')
      let cycle := pB.cons hz.1
      have hcycle : cycle.IsCycle := (SimpleGraph.Walk.cons_isCycle_iff pB hz.1).mpr ⟨hpB, hnot⟩
      have hcycleLen : cycle.length ≤ 2 * r + 1 := by
        simpa only [cycle, SimpleGraph.Walk.length_cons, pB, SimpleGraph.Walk.mapLe,
          SimpleGraph.Walk.length_map] using Nat.add_le_add_right hlen 1
      have hlocalized := hcycles a cycle hcycle hcycleLen
      obtain ⟨F, _, _, _, hcode, hsupport⟩ :=
        fundamental_even_cycle_of_path_with_support B D.tree hDB hz.1 hz.2 p hp
      refine ⟨F, hcode, ?_⟩
      intro v hv hs
      have hpv : v ∈ p.support := by rw [hsupport] at hs; exact hs
      have hpBv : v ∈ pB.support := by
        simpa only [pB, SimpleGraph.Walk.mapLe, SimpleGraph.Walk.support_map,
          SimpleGraph.Hom.coe_ofLE, List.map_id] using hpv
      exact hv (hlocalized v (by simp only [cycle, SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr hpBv))
  let gen : (B \ D.tree).edgeSet → EvenEdgeSubgraph B := fun e => Classical.choose (hgens e)
  have hcode : ∀ e, evenSubgraphCode B D.tree (gen e) = {e} := fun e => (Classical.choose_spec (hgens e)).1
  have havoid : ∀ e, ∀ v ∈ A, v ∉ (gen e).val.support := fun e => (Classical.choose_spec (hgens e)).2
  have hall := even_subgraphs_avoid_of_generators B D.tree D.tree_isTree.IsAcyclic A gen hcode havoid C
  intro v hv
  exact Classical.byContradiction (fun hn => hall v hn hv)

end LocalLaw
