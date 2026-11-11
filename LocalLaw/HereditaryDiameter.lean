import LocalLaw.BallCycleWitness
import LocalLaw.CycleSpaceCounting
import LocalLaw.ComponentModel

/-! # Intrinsic diameter after arbitrary vertex restriction

A shortest-distance spanning tree has root height at most D. Every simple
ambient path splits at its off-tree edges into at most excess+1 tree paths,
each of length at most 2D. This bounds intrinsic distances in every induced
subset, without any neighborhood-capture hypothesis.
-/

noncomputable section
set_option maxHeartbeats 2500000
namespace LocalLaw
local instance hereditaryDiameterDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section WalkSplitting
variable {V : Type*} {G T : SimpleGraph V} (hTG : T≤G)

/-- Stop at the first edge outside the chosen subgraph. -/
theorem walk_first_outside_subgraph {u v : V} (p : G.Walk u v) :
    (∃q:T.Walk u v,q.mapLe hTG=p) ∨
      ∃x y,∃q:T.Walk u x,∃h:G.Adj x y,∃r:G.Walk y v,
        ¬T.Adj x y ∧ p=(q.mapLe hTG).append (r.cons h) := by
  induction p with
  | nil => exact Or.inl ⟨SimpleGraph.Walk.nil,rfl⟩
  | @cons u a v hua p ih =>
    by_cases ht : T.Adj u a
    · rcases ih with ⟨q,hq⟩|⟨x,y,q,h,r,hn,heq⟩
      · apply Or.inl
        refine ⟨q.cons ht,?_⟩
        rw [←hq]
        rfl
      · apply Or.inr
        refine ⟨x,y,q.cons ht,h,r,hn,?_⟩
        rw [heq]
        rfl
    · exact Or.inr ⟨u,a,SimpleGraph.Walk.nil,hua,p,ht,rfl⟩

def outsideSubgraphCount {u v : V} (p : G.Walk u v) (T : SimpleGraph V) : ℕ :=
  p.edges.countP (fun e => decide (e∉T.edgeSet))

theorem outsideSubgraphCount_mapLe {u v : V} (q : T.Walk u v) :
    outsideSubgraphCount (q.mapLe hTG) T=0 := by
  have he : (q.mapLe hTG).edges=q.edges := by
    simp only [SimpleGraph.Walk.mapLe,SimpleGraph.Walk.edges_map,
      SimpleGraph.Hom.coe_ofLE,Sym2.map_id,List.map_id]
  rw [outsideSubgraphCount,he]
  apply List.countP_eq_zero.mpr
  intro e he
  simp only [decide_eq_true_eq,not_not]
  exact q.edges_subset_edgeSet he

include hTG in
/-- A simple path is divided into bounded subgraph paths by its exceptional
edges. The path may have arbitrary endpoints and length. -/
theorem path_length_le_outside_count (D : ℕ)
    (hpaths : ∀{a b:V}(q:T.Walk a b),q.IsPath→q.length≤D)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    p.length≤(outsideSubgraphCount p T+1)*(D+1) := by
  have haux : ∀n:ℕ,∀{a b:V}(r:G.Walk a b),r.length=n → r.IsPath →
      r.length≤(outsideSubgraphCount r T+1)*(D+1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b r hlen hr
      rcases walk_first_outside_subgraph hTG r with ⟨q,hq⟩|⟨x,y,q,h,s,ht,heq⟩
      · have hqp : q.IsPath := by
          have hh : (q.mapLe hTG).IsPath := hq.symm ▸ hr
          exact hh.of_mapLe
        have hqbound := hpaths q hqp
        rw [←hq,outsideSubgraphCount_mapLe hTG]
        simpa only [SimpleGraph.Walk.length_map,zero_add,one_mul] using hqbound.trans (Nat.le_succ D)
      · have hr' : ((q.mapLe hTG).append (s.cons h)).IsPath := heq ▸ hr
        have hqp : q.IsPath := hr'.of_append_left.of_mapLe
        have hsp : s.IsPath := hr'.of_append_right.of_cons
        have hqbound := hpaths q hqp
        have hslt : s.length<n := by
          rw [heq,SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_map,
            SimpleGraph.Walk.length_cons] at hlen
          omega
        have hsbound := ih s.length hslt s rfl hsp
        have heoff : decide (s(x,y)∉T.edgeSet)=true := by
          simpa only [decide_eq_true_eq,SimpleGraph.mem_edgeSet] using ht
        have hcount : outsideSubgraphCount r T=outsideSubgraphCount s T+1 := by
          rw [heq]
          simp only [outsideSubgraphCount,SimpleGraph.Walk.edges_append,SimpleGraph.Walk.edges_cons,
            List.countP_append,List.countP_cons,heoff,ite_true]
          change outsideSubgraphCount (q.mapLe hTG) T+(outsideSubgraphCount s T+1)=_
          rw [outsideSubgraphCount_mapLe hTG,zero_add]
          rfl
        rw [hcount,heq,SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_map,
          SimpleGraph.Walk.length_cons]
        nlinarith
  exact haux p.length p rfl hp

end WalkSplitting

section FiniteCounting
variable {V : Type*} [Fintype V] [DecidableEq V] {G T : SimpleGraph V}

theorem outsideSubgraphCount_le_off_edges {u v:V}(p:G.Walk u v)(hp:p.IsPath) :
    outsideSubgraphCount p T≤Nat.card (G\T).edgeSet := by
  let l:=p.edges.filter (fun e=>decide (e∉T.edgeSet))
  have hnd : l.Nodup := hp.edges_nodup.filter _
  have hcard : l.toFinset.card=outsideSubgraphCount p T := by
    rw [List.toFinset_card_of_nodup hnd]
    exact List.countP_eq_length_filter.symm
  have hsub : l.toFinset⊆(G\T).edgeFinset := by
    intro e he
    have hh : e∈p.edges ∧e∉T.edgeSet := by
      simpa only [l,List.mem_toFinset,List.mem_filter,decide_eq_true_eq] using he
    apply SimpleGraph.mem_edgeFinset.mpr
    rw [SimpleGraph.edgeSet_sdiff]
    exact ⟨p.edges_subset_edgeSet hh.1,hh.2⟩
  have hle:=Finset.card_le_card hsub
  rw [hcard,SimpleGraph.edgeFinset_card,←Nat.card_eq_fintype_card] at hle
  exact hle

omit [Fintype V] [DecidableEq V] in
theorem connected_parent_exists (G:SimpleGraph V)(hG:G.Connected)(o:V)
    (v:{v:V //v≠o}) :
    ∃u:V,G.Adj v.val u ∧G.dist o u+1=G.dist o v.val := by
  have hvpos : 0<G.dist o v.val := hG.pos_dist_of_ne (Ne.symm v.property)
  let n:=G.dist o v.val-1
  have hn : n+1=G.dist o v.val := Nat.sub_add_cancel hvpos
  have hcoe : (G.dist o v.val:ℕ∞)=G.edist o v.val :=
    ENat.coe_toNat ((G.edist_ne_top_iff_reachable).mpr (hG o v.val))
  have hvdist : G.edist o v.val=(n+1:ℕ) := by rw [hn,hcoe]
  obtain ⟨u,huv,hu⟩:=edist_succ_parent G o v.val n hvdist
  refine ⟨u,huv.symm,?_⟩
  have hud : G.dist o u=n := by simp only [SimpleGraph.dist,hu,ENat.toNat_coe]
  rw [hud,hn]

def connectedHeightParents (G:SimpleGraph V)(hG:G.Connected)(o:V) : HeightParentData V where
  root:=o
  height:=G.dist o
  height_zero v := by rw [hG.dist_eq_zero_iff];exact eq_comm
  parent v:=Classical.choose (connected_parent_exists G hG o v)
  parent_height v:=(Classical.choose_spec (connected_parent_exists G hG o v)).2

omit [Fintype V] [DecidableEq V] in
theorem connectedHeightParents_le (G:SimpleGraph V)(hG:G.Connected)(o:V) :
    (connectedHeightParents G hG o).tree≤G :=
  (connectedHeightParents G hG o).tree_le G (fun v =>
    (Classical.choose_spec (connected_parent_exists G hG o v)).1)

/-- Every simple path in a connected bounded-excess graph has controlled
length. Shortcuts through vertices later deleted do not invalidate this bound. -/
theorem connected_path_length_le_excess_diameter (G:SimpleGraph V)(hG:G.Connected)
    (D:ℕ)(hD:∀a b,G.dist a b≤D){u v:V}(p:G.Walk u v)(hp:p.IsPath) :
    p.length≤(graphExcess G+1)*(2*D+1) := by
  let P:=connectedHeightParents G hG u
  have hTG : P.tree≤G := connectedHeightParents_le G hG u
  have hT : P.tree.IsTree := P.tree_isTree
  have hpaths : ∀{a b:V}(q:P.tree.Walk a b),q.IsPath→q.length≤2*D := by
    intro a b q hq
    obtain ⟨pa,hpa⟩:=P.walk_to_root a
    obtain ⟨pb,hpb⟩:=P.walk_to_root b
    have hdist := SimpleGraph.dist_le (pa.append pb.reverse)
    rw [←acyclic_path_length_eq_dist hT.IsAcyclic q hq] at hdist
    simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse,hpa,hpb] at hdist
    have ha:=hD u a
    have hb:=hD u b
    change q.length≤2*D
    change q.length≤G.dist u a+G.dist u b at hdist
    omega
  have hpath:=path_length_le_outside_count hTG (2*D) hpaths p hp
  have hcount:=outsideSubgraphCount_le_off_edges (T:=P.tree) p hp
  rw [off_tree_edge_count G P.tree hG hTG hT] at hcount
  exact hpath.trans (Nat.mul_le_mul_right (2*D+1) (Nat.add_le_add_right hcount 1))

/-- Every induced subset inherits an intrinsic diameter bound from ambient
diameter and excess, even when that subset is disconnected. -/
theorem connected_induce_intrinsic_diameter (G:SimpleGraph V)(hG:G.Connected)
    (Ω D:ℕ)(hΩ:graphExcess G≤Ω)(hD:∀a b,G.dist a b≤D)
    (S:Set V)(a b:S) : (G.induce S).dist a b≤(Ω+1)*(2*D+1) := by
  by_cases hr : (G.induce S).Reachable a b
  · obtain ⟨p,hp,hlen⟩:=hr.exists_path_of_dist
    let e:=SimpleGraph.Embedding.induce (G:=G) S
    have hlenbound:=connected_path_length_le_excess_diameter G hG D hD
      (p.map e.toHom) (SimpleGraph.Walk.map_isPath_of_injective e.injective hp)
    simp only [SimpleGraph.Walk.length_map,hlen] at hlenbound
    exact hlenbound.trans (Nat.mul_le_mul_right (2*D+1) (Nat.add_le_add_right hΩ 1))
  · rw [SimpleGraph.dist_eq_zero_of_not_reachable hr]
    exact Nat.zero_le _

omit [Fintype V] [DecidableEq V] in
theorem walk_restrict_component_map (G:SimpleGraph V)(C:G.ConnectedComponent)
    {a b:V}(p:G.Walk a b)(ha:a∈C.supp)(hb:b∈C.supp) :
    ∃q:(G.induce C.supp).Walk ⟨a,ha⟩ ⟨b,hb⟩,
      q.map (SimpleGraph.Embedding.induce (G:=G) C.supp).toHom=p := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil,rfl⟩
  | @cons a u b hau p ih =>
    have hu:u∈C.supp := (C.mem_supp_congr_adj hau).mp ha
    obtain ⟨q,hq⟩:=ih hu hb
    have hau':(G.induce C.supp).Adj ⟨a,ha⟩ ⟨u,hu⟩ := hau
    refine ⟨q.cons hau',?_⟩
    rw [SimpleGraph.Walk.map_cons,hq]

/-- Componentwise excess is sufficient: no sum of excess over unrelated
ambient components enters the constant. -/
theorem componentwise_path_length_le_excess_diameter (G:SimpleGraph V)(Ω D:ℕ)
    (hΩ:∀C:G.ConnectedComponent,graphExcess (G.induce C.supp)≤Ω)
    (hD:∀a b,G.dist a b≤D){u v:V}(p:G.Walk u v)(hp:p.IsPath) :
    p.length≤(Ω+1)*(2*D+1) := by
  let C:=G.connectedComponentMk u
  have hu:u∈C.supp := rfl
  have hv:v∈C.supp := SimpleGraph.ConnectedComponent.sound p.reachable.symm
  obtain ⟨q,hq⟩:=walk_restrict_component_map G C p hu hv
  have hqp:q.IsPath := by
    have hh:(q.map (SimpleGraph.Embedding.induce (G:=G) C.supp).toHom).IsPath := hq.symm ▸ hp
    exact hh.of_map
  have hcut : ∀a∈C.supp,∀b∉C.supp,¬G.Adj a b := by
    intro a ha b hb hab
    exact hb ((C.mem_supp_congr_adj hab).mp ha)
  have hDC : ∀a b:C.supp,(G.induce C.supp).dist a b≤D := by
    intro a b
    rw [isolated_induce_distance G C.supp hcut]
    exact hD a.val b.val
  have hbound:=connected_path_length_le_excess_diameter (G.induce C.supp)
    C.connected_induce_supp D hDC q hqp
  have hlen:q.length=p.length := by
    simpa only [SimpleGraph.Walk.length_map] using congrArg (fun r:G.Walk u v=>r.length) hq
  rw [hlen] at hbound
  exact hbound.trans (Nat.mul_le_mul_right (2*D+1) (Nat.add_le_add_right (hΩ C) 1))

/-- The fully disconnected version needed for arbitrary retained endpoint
sets. Natural distance at an unreachable pair is zero, as in mathlib. -/
theorem componentwise_induce_intrinsic_diameter (G:SimpleGraph V)(Ω D:ℕ)
    (hΩ:∀C:G.ConnectedComponent,graphExcess (G.induce C.supp)≤Ω)
    (hD:∀a b,G.dist a b≤D)(S:Set V)(a b:S) :
    (G.induce S).dist a b≤(Ω+1)*(2*D+1) := by
  by_cases hr : (G.induce S).Reachable a b
  · obtain ⟨p,hp,hlen⟩:=hr.exists_path_of_dist
    let e:=SimpleGraph.Embedding.induce (G:=G) S
    have hbound:=componentwise_path_length_le_excess_diameter G Ω D hΩ hD
      (p.map e.toHom) (SimpleGraph.Walk.map_isPath_of_injective e.injective hp)
    simpa only [SimpleGraph.Walk.length_map,hlen] using hbound
  · rw [SimpleGraph.dist_eq_zero_of_not_reachable hr]
    exact Nat.zero_le _

theorem componentwise_induce_intrinsic_diameter_coarse (G:SimpleGraph V)(Ω D:ℕ)
    (hΩ:∀C:G.ConnectedComponent,graphExcess (G.induce C.supp)≤Ω)
    (hD:∀a b,G.dist a b≤D)(S:Set V)(a b:S) :
    (G.induce S).dist a b≤(2*(Ω+1))*(D+1) := by
  have h:=componentwise_induce_intrinsic_diameter G Ω D hΩ hD S a b
  nlinarith

end FiniteCounting
end LocalLaw
