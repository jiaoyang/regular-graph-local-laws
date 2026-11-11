import LocalLaw.SeparatedTreeGluing
import LocalLaw.ResamplingGeometricGood

/-!
# Constructing the actual resampling I-test from separated tree neighborhoods

The boundary-root ball and sampled-edge pair ball are disjoint induced trees
when their roots are farther than 2r+1. Inserting the new edge joins them
into one actual tree. Distinctness and absence of the new edge follow from
the same distance bound.
-/

noncomputable section
namespace LocalLaw

local instance tripleTreeTestDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*}

theorem graphBalls_disjoint_of_edist_gt (G : SimpleGraph V) (a b : V) (r : ℕ)
    (hfar : ((2 * r : ℕ) : ℕ∞) < G.edist a b) :
    Disjoint (graphBallVertices G a r) (graphBallVertices G b r) := by
  apply Set.disjoint_left.mpr
  intro x hax hbx
  apply (not_lt_of_ge ?_) hfar
  calc
    _ ≤ G.edist a x + G.edist x b := G.edist_triangle
    _ ≤ (r : ℕ∞) + (r : ℕ∞) := add_le_add hax (by rwa [SimpleGraph.edist_comm])
    _ ≤ ((2 * r : ℕ) : ℕ∞) := by exact_mod_cast (show r + r ≤ 2 * r by omega)

theorem graphBalls_no_edge_of_edist_gt (G : SimpleGraph V) (a b : V) (r : ℕ)
    (hfar : ((2 * r + 1 : ℕ) : ℕ∞) < G.edist a b) :
    ∀ x ∈ graphBallVertices G a r, ∀ y ∈ graphBallVertices G b r, ¬ G.Adj x y := by
  intro x hx y hy hxy
  apply (not_lt_of_ge ?_) hfar
  calc
    _ ≤ G.edist a x + (G.edist x y + G.edist y b) :=
      (G.edist_triangle (u := a) (v := x) (w := b)).trans
        (add_le_add_left (G.edist_triangle (u := x) (v := y) (w := b)) (G.edist a x))
    _ ≤ (r : ℕ∞) + (1 + (r : ℕ∞)) := add_le_add hx (add_le_add
      (le_of_eq (SimpleGraph.edist_eq_one_iff_adj.mpr hxy)) (by rwa [SimpleGraph.edist_comm]))
    _ ≤ ((2 * r + 1 : ℕ) : ℕ∞) := by exact_mod_cast (show r + (1 + r) ≤ 2 * r + 1 by omega)

theorem graphBall_isTree_mono (G : SimpleGraph V) (a : V) {r R : ℕ} (hr : r ≤ R)
    (hTree : (graphBall G a R).IsTree) : (graphBall G a r).IsTree := by
  let f : graphBall G a r →g graphBall G a R :=
    { toFun := fun v => ⟨v.val, graphBallVertices_mono G a hr v.property⟩
      map_rel' := fun h => h }
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun v : graphBallVertices G a R => v.val) h)
  refine ⟨graphBall_connected G a r, ?_⟩
  intro v p hp
  exact hTree.IsAcyclic (p.map f) (hp.map hf)

theorem pairBall_isTree_mono (G : SimpleGraph V) (b c : V) (hbc : G.Adj b c)
    {r R : ℕ} (hr : r ≤ R) (hTree : (pairBallGraph G b c R).IsTree) :
    (pairBallGraph G b c r).IsTree := by
  let f : pairBallGraph G b c r →g pairBallGraph G b c R :=
    { toFun := fun v => ⟨v.val, v.property.imp
        (fun h => h.trans (ENat.coe_le_coe.mpr hr)) (fun h => h.trans (ENat.coe_le_coe.mpr hr))⟩
      map_rel' := fun h => h }
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun v : pairBallVertices G b c R => v.val) h)
  refine ⟨pairBall_connected_of_adj G hbc r, ?_⟩
  intro v p hp
  exact hTree.IsAcyclic (p.map f) (hp.map hf)

variable [Fintype V]

theorem augmented_triple_ball_isTree (G : SimpleGraph V) (a b c : V) (r : ℕ)
    (hA : (graphBall G a r).IsTree) (hB : (pairBallGraph G b c r).IsTree)
    (hfarb : ((2 * r + 1 : ℕ) : ℕ∞) < G.edist a b)
    (hfarc : ((2 * r + 1 : ℕ) : ℕ∞) < G.edist a c) :
    ((G ⊔ SimpleGraph.edge a b).induce (graphSetBall G {a, b, c} r)).IsTree := by
  have hmono : ((2 * r : ℕ) : ℕ∞) ≤ ((2 * r + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_succ (2 * r)
  have hdisb := graphBalls_disjoint_of_edist_gt G a b r (hmono.trans_lt hfarb)
  have hdisc := graphBalls_disjoint_of_edist_gt G a c r (hmono.trans_lt hfarc)
  have hdis : Disjoint (graphBallVertices G a r) (pairBallVertices G b c r) := by
    apply Set.disjoint_left.mpr
    intro x hx hpair
    rcases hpair with hb | hc
    · exact Set.disjoint_left.mp hdisb hx hb
    · exact Set.disjoint_left.mp hdisc hx hc
  have hcross : ∀ x ∈ graphBallVertices G a r, ∀ y ∈ pairBallVertices G b c r, ¬ G.Adj x y := by
    intro x hx y hy
    rcases hy with hy | hy
    · exact graphBalls_no_edge_of_edist_gt G a b r hfarb x hx y hy
    · exact graphBalls_no_edge_of_edist_gt G a c r hfarc x hx y hy
  have hN : graphSetBall G {a, b, c} r = graphBallVertices G a r ∪ pairBallVertices G b c r := by
    ext v
    simp [graphSetBall, graphBallVertices, pairBallVertices, or_assoc]
  rw [hN]
  exact induce_union_add_bridge_isTree G _ _ hdis hcross a b (by simp [graphBallVertices])
    (Or.inl (by simp)) hA hB

theorem resamplingTreeTest_of_separated_trees (G : SimpleGraph V) (T : Set V)
    (selector h R : ℕ) (hsel : selector ≤ h) (hselR : selector ≤ R)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hA : (graphBall (outsideGraph G T) (boundaryOutsideVertex G T α) h).IsTree)
    (hB : (pairBallGraph (outsideGraph G T) (sampledFirstOutsideVertex G T S α)
      (sampledSecondOutsideVertex G T S α) R).IsTree)
    (hfarb : ((2 * selector + 1 : ℕ) : ℕ∞) < (outsideGraph G T).edist
      (boundaryOutsideVertex G T α) (sampledFirstOutsideVertex G T S α))
    (hfarc : ((2 * selector + 1 : ℕ) : ℕ∞) < (outsideGraph G T).edist
      (boundaryOutsideVertex G T α) (sampledSecondOutsideVertex G T S α)) :
    ResamplingTreeTest G T selector S α := by
  let H := outsideGraph G T
  let a := boundaryOutsideVertex G T α
  let b := sampledFirstOutsideVertex G T S α
  let c := sampledSecondOutsideVertex G T S α
  have hOne : (1 : ℕ∞) ≤ ((2 * selector + 1 : ℕ) : ℕ∞) := by
    exact_mod_cast (show 1 ≤ 2 * selector + 1 by omega)
  refine ⟨?_, ?_, ?_⟩
  · intro hab
    rw [hab, SimpleGraph.edist_self] at hfarb
    exact (not_lt_of_ge (bot_le : (0 : ℕ∞) ≤ _)) hfarb
  · intro hab
    rw [SimpleGraph.edist_eq_one_iff_adj.mpr hab] at hfarb
    exact (not_lt_of_ge hOne) hfarb
  · have htree := augmented_triple_ball_isTree H a b c selector
      (graphBall_isTree_mono H a hsel hA)
      (pairBall_isTree_mono H b c (S α).property.1 hselR hB) hfarb hfarc
    have htriple : outsideTriple G T S α = {a, b, c} := by
      ext x
      simp only [outsideTriple_mem_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      rfl
    change ((H ⊔ SimpleGraph.edge a b).induce (graphSetBall H (outsideTriple G T S α) selector)).IsTree
    rwa [htriple]

end LocalLaw
