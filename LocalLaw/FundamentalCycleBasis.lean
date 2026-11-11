import LocalLaw.CycleWalkEmbedding
import LocalLaw.CycleSpaceCounting

/-!
# Actual fundamental even cycles

A simple path in a tree plus one missing edge gives an actual even edge
pattern whose off-tree code is exactly that edge. The supported vertex count
retains the path-length bound, so a shortest-distance parent tree gives the
literal 2r+1 scale needed by local resampling geometry.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
namespace LocalLaw

local instance fundamentalCycleDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V]

def walkCycleEdgeGraph {G : SimpleGraph V} {v : V} (p : G.Walk v v) (hp : p.IsCycle) :
    SimpleGraph V := (SimpleGraph.cycleGraph p.length).map (cycleWalkInjection p hp)

omit [Fintype V] in
theorem walkCycleEdgeGraph_le {G : SimpleGraph V} {v : V} (p : G.Walk v v) (hp : p.IsCycle) :
    walkCycleEdgeGraph p hp ≤ G := by
  rw [walkCycleEdgeGraph, SimpleGraph.map_le_iff_le_comap]
  intro i j hij
  exact cycleWalkInjection_adj p hp i j hij

theorem walkCycleEdgeGraph_even {G : SimpleGraph V} {v : V} (p : G.Walk v v) (hp : p.IsCycle) :
    ∀ w, Even ((walkCycleEdgeGraph p hp).degree w) := by
  intro w
  let f := cycleWalkInjection p hp
  by_cases hw : w ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hw
    have h := mappedPattern_degree_image (SimpleGraph.cycleGraph p.length) f i
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h ⊢
    change Even (Nat.card (((SimpleGraph.cycleGraph p.length).map f).neighborSet (f i)))
    rw [h]
    have htwo := cycleGraph_degree p.length hp.three_le_length i
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at htwo
    rw [htwo]
    decide
  · have h := mappedPattern_degree_outside (SimpleGraph.cycleGraph p.length) f w hw
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h ⊢
    change Even (Nat.card (((SimpleGraph.cycleGraph p.length).map f).neighborSet w))
    rw [h]
    exact Even.zero

theorem walkCycleEdgeGraph_support_card {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :
    (walkCycleEdgeGraph p hp).support.toFinset.card ≤ p.length := by
  have hsub : (walkCycleEdgeGraph p hp).support.toFinset ⊆
      (Finset.univ : Finset (Fin p.length)).image (cycleWalkInjection p hp) := by
    intro w hw
    obtain ⟨z, hwz⟩ := ((walkCycleEdgeGraph p hp).mem_support).mp (Set.mem_toFinset.mp hw)
    obtain ⟨i, j, hij, hi, hj⟩ := (SimpleGraph.map_adj (cycleWalkInjection p hp)
      (SimpleGraph.cycleGraph p.length) w z).mp hwz
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  exact (Finset.card_le_card hsub).trans (by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (s := (Finset.univ : Finset (Fin p.length))) (f := cycleWalkInjection p hp)))

theorem walkCycleEdgeGraph_support {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :
    (walkCycleEdgeGraph p hp).support = {w | w ∈ p.support} := by
  ext w
  constructor
  · intro hw
    obtain ⟨z, hwz⟩ := ((walkCycleEdgeGraph p hp).mem_support).mp hw
    obtain ⟨i, j, hij, hi, hj⟩ := (SimpleGraph.map_adj (cycleWalkInjection p hp)
      (SimpleGraph.cycleGraph p.length) w z).mp hwz
    exact hi ▸ p.getVert_mem_support i.val
  · intro hw
    obtain ⟨k, hk, hkle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
    have hwimage : w ∈ Set.range (cycleWalkInjection p hp) := by
      by_cases hlt : k < p.length
      · exact ⟨⟨k, hlt⟩, hk⟩
      · have heq : k = p.length := by omega
        have hwv : w = v := by rw [heq, p.getVert_length] at hk; exact hk.symm
        refine ⟨⟨0, by have h := hp.three_le_length; omega⟩, ?_⟩
        change p.getVert 0 = w
        rw [p.getVert_zero, hwv]
    obtain ⟨i, rfl⟩ := hwimage
    have himage := mappedPattern_degree_image (SimpleGraph.cycleGraph p.length) (cycleWalkInjection p hp) i
    have htwo := cycleGraph_degree p.length hp.three_le_length i
    have hpos : 0 < (walkCycleEdgeGraph p hp).degree (cycleWalkInjection p hp i) := by
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        at himage htwo ⊢
      change 0 < Nat.card (((SimpleGraph.cycleGraph p.length).map (cycleWalkInjection p hp)).neighborSet _)
      rw [himage, htwo]
      decide
    exact ((walkCycleEdgeGraph p hp).degree_pos_iff_mem_support _).mp hpos

private theorem cycleGraph_zero_one_adj (n : ℕ) (hn : 3 ≤ n) :
    (SimpleGraph.cycleGraph n).Adj ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n =>
      apply SimpleGraph.cycleGraph_adj.mpr
      apply Or.inr
      have hz : (⟨0, by omega⟩ : Fin (n + 1 + 1)) = 0 := rfl
      rw [hz, sub_zero]
      apply Fin.ext
      simp [Nat.mod_eq_of_lt (show 1 < n + 1 + 1 by omega)]

omit [Fintype V] in
theorem walkCycleEdgeGraph_first_edge {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) (p : G.Walk b a) (hp : (p.cons hab).IsCycle) :
    (walkCycleEdgeGraph (p.cons hab) hp).Adj a b := by
  let c := p.cons hab
  have hn : 3 ≤ c.length := hp.three_le_length
  let i : Fin c.length := ⟨0, by omega⟩
  let j : Fin c.length := ⟨1, by omega⟩
  have hij : (SimpleGraph.cycleGraph c.length).Adj i j := cycleGraph_zero_one_adj c.length hn
  have h : ((SimpleGraph.cycleGraph c.length).map (cycleWalkInjection c hp)).Adj
      (cycleWalkInjection c hp i) (cycleWalkInjection c hp j) := SimpleGraph.map_adj_apply.mpr hij
  change (walkCycleEdgeGraph c hp).Adj
    (cycleWalkInjection c hp i) (cycleWalkInjection c hp j) at h
  have hi : cycleWalkInjection c hp i = a := rfl
  have hj : cycleWalkInjection c hp j = b := by
    change (p.cons hab).getVert (0 + 1) = b
    simp only [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_zero]
  rwa [hi, hj] at h

/-- An actual simple tree path and a missing edge give a single-code even
cycle, with a quantitative supported-vertex bound. -/
theorem fundamental_even_cycle_of_path_with_support (G T : SimpleGraph V) (hTG : T ≤ G)
    {a b : V} (hab : G.Adj a b) (htab : ¬ T.Adj a b)
    (p : T.Walk b a) (hp : p.IsPath) :
    ∃ C : EvenEdgeSubgraph G,
      C.val ≤ T ⊔ SimpleGraph.edge a b ∧ C.val.Adj a b ∧
      C.val.support.toFinset.card ≤ p.length + 1 ∧
      evenSubgraphCode G T C = {⟨s(a, b), hab, htab⟩} ∧
      C.val.support = {v | v ∈ p.support} := by
  let H := T ⊔ SimpleGraph.edge a b
  have habH : H.Adj a b := Or.inr ((SimpleGraph.edge_adj a b a b).mpr
    ⟨Or.inl ⟨rfl, rfl⟩, hab.ne⟩)
  let pH := p.mapLe (show T ≤ H from le_sup_left)
  have hpH : pH.IsPath := hp.mapLe le_sup_left
  have hnot : s(a, b) ∉ pH.edges := by
    intro he
    have he' : s(a, b) ∈ p.edges := by
      simpa only [pH, SimpleGraph.Walk.mapLe, SimpleGraph.Walk.edges_map,
        SimpleGraph.Hom.coe_ofLE, Sym2.map_id, List.map_id] using he
    exact htab (p.adj_of_mem_edges he')
  let c := pH.cons habH
  have hc : c.IsCycle := (SimpleGraph.Walk.cons_isCycle_iff pH habH).mpr ⟨hpH, hnot⟩
  let A := walkCycleEdgeGraph c hc
  have hAH : A ≤ H := walkCycleEdgeGraph_le c hc
  have hHG : H ≤ G := by
    apply sup_le hTG
    intro x y hxy
    rcases (SimpleGraph.edge_adj a b x y).mp hxy with ⟨hxy, _⟩
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab
    · exact hab.symm
  let C : EvenEdgeSubgraph G := ⟨A, hAH.trans hHG, walkCycleEdgeGraph_even c hc⟩
  have hedge : A.Adj a b := walkCycleEdgeGraph_first_edge habH pH hc
  refine ⟨C, hAH, hedge, ?_, ?_, ?_⟩
  · have h := walkCycleEdgeGraph_support_card c hc
    simpa only [c, SimpleGraph.Walk.length_cons, pH, SimpleGraph.Walk.length_map] using h
  · ext e
    change e.val ∈ A.edgeSet ↔ e = ⟨s(a, b), hab, htab⟩
    constructor
    · intro he
      have hle : e.val ∈ H.edgeSet := SimpleGraph.edgeSet_mono hAH he
      have heprops : e.val ∈ G.edgeSet ∧ e.val ∉ T.edgeSet := by
        simpa only [SimpleGraph.edgeSet_sdiff, Set.mem_diff] using e.property
      have hnt : e.val ∉ T.edgeSet := heprops.2
      have heq : e.val = s(a, b) := by
        simpa only [H, SimpleGraph.edgeSet_sup, SimpleGraph.edge_edgeSet_of_ne hab.ne,
          Set.mem_union, Set.mem_singleton_iff, hnt, false_or] using hle
      exact Subtype.ext heq
    · intro he
      subst e
      exact hedge
  · change A.support = {v | v ∈ p.support}
    rw [walkCycleEdgeGraph_support c hc]
    have hsupport : pH.support = p.support := by
      simp only [pH, SimpleGraph.Walk.mapLe, SimpleGraph.Walk.support_map,
        SimpleGraph.Hom.coe_ofLE, List.map_id]
    ext v
    change v ∈ c.support ↔ v ∈ p.support
    simp only [c, SimpleGraph.Walk.support_cons, List.mem_cons, hsupport]
    constructor
    · rintro (rfl | hv)
      · exact p.end_mem_support
      · exact hv
    · exact Or.inr

/-- The original compact interface, preserving the quantitative path bound. -/
theorem fundamental_even_cycle_of_path (G T : SimpleGraph V) (hTG : T ≤ G)
    {a b : V} (hab : G.Adj a b) (htab : ¬ T.Adj a b)
    (p : T.Walk b a) (hp : p.IsPath) :
    ∃ C : EvenEdgeSubgraph G,
      C.val ≤ T ⊔ SimpleGraph.edge a b ∧ C.val.Adj a b ∧
      C.val.support.toFinset.card ≤ p.length + 1 ∧
      evenSubgraphCode G T C = {⟨s(a, b), hab, htab⟩} := by
  obtain ⟨C, h₁, h₂, h₃, h₄, _⟩ := fundamental_even_cycle_of_path_with_support G T hTG hab htab p hp
  exact ⟨C, h₁, h₂, h₃, h₄⟩

/-- The support is an actual connected subtree of the spanning tree. -/
theorem fundamental_even_cycle_with_connected_tree_support (G T : SimpleGraph V) (hTG : T ≤ G)
    {a b : V} (hab : G.Adj a b) (htab : ¬ T.Adj a b)
    (p : T.Walk b a) (hp : p.IsPath) :
    ∃ C : EvenEdgeSubgraph G,
      evenSubgraphCode G T C = {⟨s(a, b), hab, htab⟩} ∧
      C.val.support.toFinset.card ≤ p.length + 1 ∧ (T.induce C.val.support).Connected := by
  obtain ⟨C, _, _, hsize, hcode, hsupport⟩ :=
    fundamental_even_cycle_of_path_with_support G T hTG hab htab p hp
  refine ⟨C, hcode, hsize, ?_⟩
  rw [hsupport]
  exact p.connected_induce_support

end LocalLaw
