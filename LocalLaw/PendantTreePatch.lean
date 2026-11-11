import LocalLaw.ResamplingEvenPatternExclusion
import LocalLaw.EvenPatternRestriction

/-!
# A short even pattern cannot enter a split tree patch

Inside W the new graph is a subgraph of an old tree with the edge b-c
removed. Its only new outward edges are b-a and c-l. An even pattern on at
most R+1 supported vertices cannot use an old outward edge: its component
path followed by that edge would reach outside W within R. The two new
attachment edges belong to separate tree components. Cut parity and the
even-forest lemma therefore exclude either root from the pattern.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw

local instance pendantTreePatchDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V]

theorem outside_component_card_add_one_le_support (F : SimpleGraph V) (T : Set V)
    (C : CutComponent F T) (x : C.supp) (hx : x.val.val ∈ F.support)
    (e : CutBoundaryEdge F T C) : Nat.card C.supp + 1 ≤ F.support.toFinset.card := by
  let enc : C.supp ⊕ Unit → F.support := fun z => match z with
    | Sum.inl y => ⟨y.val.val, outside_component_supported F T C x hx y⟩
    | Sum.inr _ => ⟨e.val.val.1, (F.mem_support).mpr ⟨e.val.val.2, e.val.property.1⟩⟩
  have hinj : Function.Injective enc := by
    intro a b h
    have hraw := congrArg (fun y : F.support => y.val) h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext (Subtype.ext hraw))
      | inr b =>
        change a.val.val = e.val.val.1 at hraw
        exact False.elim (a.val.property (hraw.symm ▸ e.val.property.2.1))
    | inr a =>
      cases b with
      | inl b =>
        change e.val.val.1 = b.val.val at hraw
        exact False.elim (b.val.property (hraw ▸ e.val.property.2.1))
      | inr b => exact congrArg Sum.inr (Subsingleton.elim a b)
  have h := Nat.card_le_card_of_injective enc hinj
  simpa only [Nat.card_sum, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_unit,
    Set.toFinset_card] using h

/-- The first root of an actual split tree patch is excluded from every
short even subgraph. All patch assumptions are pointwise edge/metric facts. -/
theorem even_pattern_avoids_split_tree_root (G H : SimpleGraph V) (W : Set V)
    (b c a l : V) (hb : b ∈ W) (hc : c ∈ W) (hbc : G.Adj b c)
    (htree : (G.induce W).IsTree) (R : ℕ)
    (hfar : ∀ v ∉ W, (R : ℕ∞) < G.edist b v)
    (hinside : ∀ u v : W, H.Adj u.val v.val →
      ((G.induce W) \ SimpleGraph.edge (⟨b, hb⟩ : W) (⟨c, hc⟩ : W)).Adj u v)
    (hcross : ∀ u ∈ W, ∀ v ∉ W, H.Adj u v → G.Adj u v ∨
      (u = b ∧ v = a) ∨ (u = c ∧ v = l))
    (F : SimpleGraph V) (hFH : F ≤ H) (heven : ∀ v, Even (F.degree v))
    (hsize : F.support.toFinset.card ≤ R + 1) : b ∉ F.support := by
  intro hbF
  let T := Wᶜ
  let bb : {v : V // v ∉ T} := ⟨b, by simpa only [T, Set.mem_compl_iff, not_not] using hb⟩
  let C : CutComponent F T := (outsideGraph F T).connectedComponentMk bb
  let x : C.supp := ⟨bb, rfl⟩
  have hW : ∀ y : C.supp, y.val.val ∈ W := by
    intro y
    simpa only [T, Set.mem_compl_iff, not_not] using y.val.property
  let D := (G.induce W) \ SimpleGraph.edge (⟨b, hb⟩ : W) (⟨c, hc⟩ : W)
  let fD : cutComponentGraph F T C →g D :=
    { toFun := fun y => ⟨y.val.val, hW y⟩
      map_rel' := fun h => hinside _ _ (hFH h) }
  have hfD : Function.Injective fD := by
    intro y z h
    exact Subtype.ext (Subtype.ext (congrArg (fun v : W => v.val) h))
  have hNoC : ∀ y : C.supp, y.val.val ≠ c := by
    intro y hyc
    obtain ⟨p, hp⟩ := C.connected_induce_supp.exists_isPath x y
    let qD := p.map fD
    let q := qD.mapLe (show D ≤ G.induce W from sdiff_le)
    have hq : q.IsPath := (SimpleGraph.Walk.map_isPath_of_injective hfD hp).mapLe sdiff_le
    have hyEq : fD y = (⟨c, hc⟩ : W) := Subtype.ext hyc
    have hxEq : fD x = (⟨b, hb⟩ : W) := rfl
    have hnot : s(fD y, fD x) ∉ q.edges := by
      intro he
      have heD : s(fD y, fD x) ∈ qD.edges := by
        simpa only [q, SimpleGraph.Walk.mapLe, SimpleGraph.Walk.edges_map,
          SimpleGraph.Hom.coe_ofLE, Sym2.map_id, List.map_id] using he
      have hbad := qD.adj_of_mem_edges heD
      have hedge : (SimpleGraph.edge (⟨b, hb⟩ : W) (⟨c, hc⟩ : W)).Adj (fD y) (fD x) := by
        rw [hyEq, hxEq]
        exact (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inr ⟨rfl, rfl⟩, fun h => hbc.ne (congrArg Subtype.val h).symm⟩
      exact hbad.2 hedge
    have hclose : (G.induce W).Adj (fD y) (fD x) := by
      rw [hyEq, hxEq]
      exact hbc.symm
    exact htree.IsAcyclic (q.cons hclose) ((SimpleGraph.Walk.cons_isCycle_iff q hclose).mpr ⟨hq, hnot⟩)
  have hboundary : ∀ e : CutBoundaryEdge F T C, e.val.val = (a, b) := by
    intro e
    let y : C.supp := ⟨⟨e.val.val.2, e.val.property.2.2⟩, e.property⟩
    have hyW : e.val.val.2 ∈ W := hW y
    have hvOut : e.val.val.1 ∉ W := e.val.property.2.1
    have heH := hFH e.val.property.1.symm
    rcases hcross e.val.val.2 hyW e.val.val.1 hvOut heH with hold | ⟨hub, hva⟩ | ⟨huc, hvl⟩
    · have hcard := outside_component_card_add_one_le_support F T C x hbF e
      have hcardR : Fintype.card C.supp ≤ R := by
        rw [Nat.card_eq_fintype_card] at hcard
        omega
      obtain ⟨p, hp⟩ := C.connected_induce_supp.exists_isPath x y
      have hlen : p.length + 1 ≤ R := by have hh := hp.length_lt; omega
      let fOld : cutComponentGraph F T C →g G :=
        { toFun := fun v => v.val.val
          map_rel' := fun {u v} h => (hinside ⟨u.val.val, hW u⟩ ⟨v.val.val, hW v⟩ (hFH h)).1 }
      let q := (p.map fOld).concat hold
      have hdist : G.edist b e.val.val.1 ≤ (R : ℕ∞) := (G.edist_le q).trans (by
        simpa only [q, SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_map] using ENat.coe_le_coe.mpr hlen)
      exact False.elim ((not_lt_of_ge hdist) (hfar e.val.val.1 hvOut))
    · exact Prod.ext hva hub
    · exact False.elim (hNoC y huc)
  have hcutle : cutMultiplicity F T C ≤ 1 := by
    let f : CutBoundaryEdge F T C → Unit := fun _ => ()
    have hf : Function.Injective f := by
      intro e g _
      exact Subtype.ext (Subtype.ext ((hboundary e).trans (hboundary g).symm))
    simpa only [cutMultiplicity, Nat.card_eq_fintype_card, Fintype.card_unit] using
      Nat.card_le_card_of_injective f hf
  have hcutzero := cutMultiplicity_eq_zero_of_even_le_one F T heven C hcutle
  have hdefzero : ∀ y : C.supp, cutDeficit F T C y = 0 := by
    intro y
    have hsum := cutMultiplicity_eq_sum_deficit F T C
    have hle : cutDeficit F T C y ≤ ∑ z : C.supp, cutDeficit F T C z :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)
    rw [hcutzero] at hsum
    simp only [← finsum_eq_sum_of_fintype] at hsum hle
    omega
  have hforest : (cutComponentGraph F T C).IsAcyclic := by
    let f : cutComponentGraph F T C →g G.induce W :=
      (SimpleGraph.Hom.ofLE (show D ≤ G.induce W from sdiff_le)).comp fD
    have hf : Function.Injective f := hfD
    intro v p hp
    exact htree.IsAcyclic (p.map f) (hp.map hf)
  have hEvenC : ∀ y : C.supp, Even ((cutComponentGraph F T C).degree y) := by
    intro y
    have h := cutComponent_ambient_degree_identity F T C y
    rw [hdefzero y, Nat.add_zero] at h
    have he := heven y.val.val
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h he ⊢
    rwa [← h]
  have hempty := even_forest_eq_bot _ hforest hEvenC
  have hdegree := cutComponent_ambient_degree_identity F T C x
  rw [hempty, hdefzero x] at hdegree
  have hpos : 0 < F.degree b := (F.degree_pos_iff_mem_support b).mpr hbF
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hdegree hpos
  have hbot : Nat.card ((⊥ : SimpleGraph C.supp).neighborSet x) = 0 := by simp
  rw [hbot, Nat.zero_add] at hdegree
  have hzero : Nat.card (F.neighborSet b) = 0 := hdegree
  omega

theorem even_pattern_avoids_split_tree_roots (G H : SimpleGraph V) (W : Set V)
    (b c a l : V) (hb : b ∈ W) (hc : c ∈ W) (hbc : G.Adj b c)
    (htree : (G.induce W).IsTree) (R : ℕ)
    (hfarb : ∀ v ∉ W, (R : ℕ∞) < G.edist b v)
    (hfarc : ∀ v ∉ W, (R : ℕ∞) < G.edist c v)
    (hinside : ∀ u v : W, H.Adj u.val v.val →
      ((G.induce W) \ SimpleGraph.edge (⟨b, hb⟩ : W) (⟨c, hc⟩ : W)).Adj u v)
    (hcross : ∀ u ∈ W, ∀ v ∉ W, H.Adj u v → G.Adj u v ∨
      (u = b ∧ v = a) ∨ (u = c ∧ v = l))
    (F : SimpleGraph V) (hFH : F ≤ H) (heven : ∀ v, Even (F.degree v))
    (hsize : F.support.toFinset.card ≤ R + 1) : b ∉ F.support ∧ c ∉ F.support := by
  refine ⟨even_pattern_avoids_split_tree_root G H W b c a l hb hc hbc htree R
    hfarb hinside hcross F hFH heven hsize, ?_⟩
  apply even_pattern_avoids_split_tree_root G H W c b l a hc hb hbc.symm htree R hfarc
    (fun u v h => ?_) (fun u hu v hv h => ?_) F hFH heven hsize
  · rw [SimpleGraph.edge_comm (⟨c, hc⟩ : W) (⟨b, hb⟩ : W)]
    exact hinside u v h
  · have hnew := hcross u hu v hv h
    tauto

end LocalLaw
