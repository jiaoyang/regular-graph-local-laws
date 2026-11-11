import LocalLaw.ShortPatchWalks
import LocalLaw.FundamentalCycleBasis
import LocalLaw.CycleArcGeometry

/-! # A short cycle cannot be reached through a split tree branch

An actual cycle has two arcs, so every one of its vertices is reached from
the chosen vertex in at most half its length. Appending those arcs to a
short entry-avoiding walk from a patch root keeps the entire cycle in the
old deleted tree. The even-forest theorem then gives a contradiction.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw

local instance shortCycleTreePatchDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V]

theorem short_cycle_not_reached_from_split_patch (G H : SimpleGraph V) (W : Set V)
    (b c a l : V) (hb : b ∈ W) (hc : c ∈ W) (hbc : G.Adj b c)
    (htree : (G.induce W).IsTree) (R r : ℕ) (hr : 2 * r ≤ R)
    (hfar : ∀ v ∉ W, (R : ℕ∞) < G.edist b v)
    (hinside : ∀ u v : W, H.Adj u.val v.val →
      ((G.induce W) \ SimpleGraph.edge (⟨b, hb⟩ : W) (⟨c, hc⟩ : W)).Adj u v)
    (hcross : ∀ u ∈ W, ∀ v ∉ W, H.Adj u v → G.Adj u v ∨
      (u = b ∧ v = a) ∨ (u = c ∧ v = l))
    {v : V} (p : H.Walk v v) (hp : p.IsCycle) (hplen : p.length ≤ 2 * r + 1)
    (q : H.Walk b v) (hqlen : q.length ≤ r) (hqentry : s(b, a) ∉ q.edges) : False := by
  classical
  let F := walkCycleEdgeGraph p hp
  have hFH : F ≤ H := walkCycleEdgeGraph_le p hp
  have heven : ∀ x, Even (F.degree x) := walkCycleEdgeGraph_even p hp
  have hsize : F.support.toFinset.card ≤ R + 1 :=
    (walkCycleEdgeGraph_support_card p hp).trans (by omega)
  have havoid : b ∉ F.support := even_pattern_avoids_split_tree_root G H W b c a l hb hc
    hbc htree R hfar hinside hcross F hFH heven hsize
  let f := cycleWalkInjection p hp
  obtain ⟨i₀, hi₀⟩ := cycleWalkInjection_root p hp
  let fF : SimpleGraph.cycleGraph p.length →g F :=
    { toFun := f
      map_rel' := fun h => SimpleGraph.map_adj_apply.mpr h }
  have hsupport : F.support ⊆ W := by
    intro w hw
    obtain ⟨z, hwz⟩ := (F.mem_support).mp hw
    obtain ⟨j, _, _, hj, _⟩ := (SimpleGraph.map_adj f (SimpleGraph.cycleGraph p.length) w z).mp hwz
    have hd : (SimpleGraph.cycleGraph p.length).edist i₀ j ≤ (r : ℕ∞) := by
      have hh := cycle_hom_edist_le_half p.length hp.three_le_length
        (show SimpleGraph.cycleGraph p.length →g SimpleGraph.cycleGraph p.length from
          { toFun := id, map_rel' := fun h => h }) i₀ j
      exact hh.trans (ENat.coe_le_coe.mpr (by omega))
    have hfinite : (SimpleGraph.cycleGraph p.length).edist i₀ j ≠ ⊤ :=
      ne_of_lt (hd.trans_lt (by simp))
    obtain ⟨arc, harc⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfinite
    have harclen : arc.length ≤ r := ENat.coe_le_coe.mp (harc ▸ hd)
    let arcF : F.Walk v w := (arc.map fF).copy hi₀ hj
    let arcH := arcF.mapLe hFH
    have hArcLength : arcH.length ≤ r := by
      simpa only [arcH, arcF, SimpleGraph.Walk.mapLe, SimpleGraph.Walk.length_map,
        SimpleGraph.Walk.length_copy] using harclen
    have hArcEntry : s(b, a) ∉ arcH.edges := by
      intro he
      have heF : s(b, a) ∈ arcF.edges := by
        simpa only [arcH, SimpleGraph.Walk.mapLe, SimpleGraph.Walk.edges_map,
          SimpleGraph.Hom.coe_ofLE, Sym2.map_id, List.map_id] using he
      exact havoid ((F.mem_support).mpr ⟨a, arcF.adj_of_mem_edges heF⟩)
    have hentry : s(b, a) ∉ (q.append arcH).edges := by
      simpa only [SimpleGraph.Walk.edges_append, List.mem_append, not_or] using
        And.intro hqentry hArcEntry
    obtain ⟨hw, _, _⟩ := short_walk_avoiding_patch_entry G H W b c a l hb hc hbc htree R
      hfar hinside hcross (q.append arcH) (by simp only [SimpleGraph.Walk.length_append]; omega) hentry
    exact hw
  let emb : W ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hsupportRange : F.support ⊆ Set.range emb := fun x hx => ⟨⟨x, hsupport hx⟩, rfl⟩
  have hforest : (F.comap emb).IsAcyclic := by
    have hle : F.comap emb ≤ G.induce W := fun x y h => (hinside x y (hFH h)).1
    exact graph_acyclic_of_le hle htree.IsAcyclic
  have hzero := even_pattern_eq_bot_of_comap_forest F emb hsupportRange heven hforest
  have hvF : v ∈ F.support := by
    rw [walkCycleEdgeGraph_support]
    exact p.start_mem_support
  rw [hzero] at hvF
  obtain ⟨w, hw⟩ := (SimpleGraph.mem_support _).mp hvF
  exact hw

theorem short_cycle_not_reached_by_common_walk_from_split_patch
    (G H : SimpleGraph V) (W : Set V)
    (b c a l : V) (hb : b ∈ W) (hc : c ∈ W) (hbc : G.Adj b c)
    (htree : (G.induce W).IsTree) (R r : ℕ) (hr : 2 * r ≤ R)
    (hfar : ∀ v ∉ W, (R : ℕ∞) < G.edist b v)
    (hinside : ∀ u v : W, H.Adj u.val v.val →
      ((G.induce W) \ SimpleGraph.edge (⟨b, hb⟩ : W) (⟨c, hc⟩ : W)).Adj u v)
    (hcross : ∀ u ∈ W, ∀ v ∉ W, H.Adj u v → G.Adj u v ∨
      (u = b ∧ v = a) ∨ (u = c ∧ v = l))
    (hnew : ¬ G.Adj b a)
    {v : V} (p : H.Walk v v) (hp : p.IsCycle) (hplen : p.length ≤ 2 * r + 1)
    (q : (G ⊓ H).Walk b v) (hqlen : q.length ≤ r) : False := by
  let qH := q.mapLe (show G ⊓ H ≤ H from inf_le_right)
  have hqentry : s(b, a) ∉ qH.edges := by
    intro he
    have heq : s(b, a) ∈ q.edges := by
      simpa only [qH, SimpleGraph.Walk.mapLe, SimpleGraph.Walk.edges_map,
        SimpleGraph.Hom.coe_ofLE, Sym2.map_id, List.map_id] using he
    exact hnew (q.adj_of_mem_edges heq).1
  exact short_cycle_not_reached_from_split_patch G H W b c a l hb hc hbc htree R r hr
    hfar hinside hcross p hp hplen qH (by simpa only [qH, SimpleGraph.Walk.mapLe,
      SimpleGraph.Walk.length_map] using hqlen) hqentry

end LocalLaw
