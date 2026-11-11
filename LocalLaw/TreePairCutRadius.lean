import LocalLaw.AdmissibleTreeBranches
import LocalLaw.DeletedTreeBallGeometry

/-! # The detached side of a two-root tree patch is the genuine cavity ball

The radius-r ball of the removed neighbor adds no extra vertices to the
other side of the bridge. This proves literal equality of vertex sets,
without a diagonal claim for neighborhoods of arbitrary additional targets.
-/

noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance treePairCutRadiusDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

def vertexDeletedBallAmbient (G : SimpleGraph V) (b : V) (c : {v : V // v ≠ b}) (r : ℕ) : Set V :=
  Set.range (fun x : graphBallVertices (G.induce {v | v ≠ b}) c r => x.val.val)

theorem pairBall_short_root_walk (G : SimpleGraph V) (b c : V) (r : ℕ)
    (root v : pairBallVertices G b c r) (hroot : root.val = b ∨ root.val = c)
    (hv : G.edist root.val v.val ≤ (r : ℕ∞)) :
    ∃ p : (pairBallGraph G b c r).Walk root v, p.length ≤ r := by
  have hfinite := ne_top_of_le_ne_top (ENat.coe_ne_top r) hv
  obtain ⟨p, hp⟩ := G.exists_walk_of_edist_ne_top hfinite
  have hlen : p.length ≤ r := ENat.coe_le_coe.mp (hp.trans_le hv)
  have hsupp : ∀ x ∈ p.support, x ∈ pairBallVertices G b c r := by
    intro x hx
    have hxroot := (G.edist_le (p.takeUntil x hx)).trans
      (ENat.coe_le_coe.mpr ((p.length_takeUntil_le hx).trans hlen))
    rcases hroot with hroot | hroot
    · exact Or.inl (by simpa only [hroot] using hxroot)
    · exact Or.inr (by simpa only [hroot] using hxroot)
  obtain ⟨q, hq⟩ := walk_lift_induced_of_support G (pairBallVertices G b c r) p hsupp
    root.property v.property
  exact ⟨q, hq.trans_le hlen⟩

theorem tree_pair_second_branch_eq_deleted_ball (G : SimpleGraph V) (b c : V) (r : ℕ)
    (hbc : G.Adj b c) (htree : (pairBallGraph G b c r).IsTree) :
    inducedTreeBranch G (pairBallVertices G b c r) (pairBallLeft G b c r)
      (pairBallRight G b c r) (pairBallRight G b c r) =
    vertexDeletedBallAmbient G b ⟨c, hbc.ne.symm⟩ r := by
  let W := pairBallVertices G b c r
  let H := pairBallGraph G b c r
  let bb := pairBallLeft G b c r
  let cc := pairBallRight G b c r
  let D := treeEdgeDeleted H bb cc
  have hNoReach : ¬D.Reachable bb cc :=
    (SimpleGraph.isBridge_iff.mp
      ((SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp htree.IsAcyclic)
        (show H.Adj bb cc from hbc))).2
  apply Set.Subset.antisymm
  · rintro v ⟨x, rfl⟩
    let xx : W := x.val
    have hreach : D.Reachable cc xx :=
      (mem_treeEdgeBranch_iff H bb cc cc xx).mp x.property
    obtain ⟨q, hqpath, _⟩ := hreach.exists_path_of_dist
    let qH : H.Walk cc xx := q.mapLe sdiff_le
    have hqHpath : qH.IsPath := hqpath.mapLe sdiff_le
    have hbavoid : bb ∉ qH.support := by
      intro hb
      have hbq : bb ∈ q.support := by
        simpa [qH, SimpleGraph.Walk.mapLe, SimpleGraph.Walk.support_map] using hb
      exact hNoReach ((q.takeUntil bb hbq).reachable.symm)
    have hlen : qH.length ≤ r := by
      rcases xx.property with hleft | hright
      · obtain ⟨p, hp⟩ := pairBall_short_root_walk G b c r bb xx (Or.inl rfl) hleft
        have hpaths := htree.IsAcyclic.path_unique
          (⟨qH.cons (show H.Adj bb cc from hbc), hqHpath.cons hbavoid⟩ : H.Path bb xx)
          ⟨p.bypass, p.bypass_isPath⟩
        have he := congrArg (fun z : H.Path bb xx => z.val.length) hpaths
        have hshort := p.length_bypass_le.trans hp
        simp only [SimpleGraph.Walk.length_cons] at he
        omega
      · obtain ⟨p, hp⟩ := pairBall_short_root_walk G b c r cc xx (Or.inr rfl) hright
        have hpaths := htree.IsAcyclic.path_unique (⟨qH, hqHpath⟩ : H.Path cc xx)
          ⟨p.bypass, p.bypass_isPath⟩
        have he := congrArg (fun z : H.Path cc xx => z.val.length) hpaths
        exact he.trans_le (p.length_bypass_le.trans hp)
    let f : H →g G := (SimpleGraph.Embedding.induce W).toHom
    let qG := qH.map f
    have hbsupp : ∀ w ∈ qG.support, w ≠ b := by
      intro w hw hwb
      rw [SimpleGraph.Walk.support_map] at hw
      obtain ⟨u, hu, he⟩ := List.mem_map.mp hw
      have hub : u = bb := Subtype.ext (he.trans hwb)
      exact hbavoid (hub ▸ hu)
    have hxb : xx.val ≠ b := hbsupp xx.val qG.end_mem_support
    obtain ⟨p, hp⟩ := walk_lift_induced_of_support G {v | v ≠ b} qG hbsupp hbc.ne.symm hxb
    refine ⟨⟨⟨xx.val, hxb⟩, ?_⟩, rfl⟩
    exact (SimpleGraph.edist_le p).trans (ENat.coe_le_coe.mpr
      (hp.trans_le (by simpa only [qG, SimpleGraph.Walk.length_map] using hlen)))
  · rintro v ⟨x, rfl⟩
    let J := graphBall (G.induce {v | v ≠ b}) (⟨c, hbc.ne.symm⟩ : {v : V // v ≠ b}) r
    let f : J →g D :=
      { toFun := fun y => ⟨y.val.val, Or.inr
          ((graphHom_edist_le (SimpleGraph.Embedding.induce (G := G) {v | v ≠ b}).toHom
            (⟨c, hbc.ne.symm⟩ : {v : V // v ≠ b}) y.val).trans y.property)⟩
        map_rel' := by
          intro y z hyz
          refine ⟨hyz, ?_⟩
          intro he
          rcases (SimpleGraph.edge_adj bb cc _ _).mp he with ⟨he, _⟩
          rcases he with ⟨hy, _⟩ | ⟨_, hz⟩
          · exact y.val.property (congrArg Subtype.val hy)
          · exact z.val.property (congrArg Subtype.val hz) }
    let root : graphBallVertices (G.induce {v | v ≠ b}) (⟨c, hbc.ne.symm⟩ : {v : V // v ≠ b}) r :=
      ⟨_, center_mem_graphBall _ _ _⟩
    obtain ⟨p⟩ := (graphBall_connected _ _ r).preconnected root x
    have hr : D.Reachable cc (f x) := (p.map f).reachable
    exact (mem_inducedTreeBranch_iff G W bb cc cc (f x)).mpr
      ((mem_treeEdgeBranch_iff H bb cc cc (f x)).mpr hr)

end LocalLaw
