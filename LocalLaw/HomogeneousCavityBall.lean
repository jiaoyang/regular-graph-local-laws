import LocalLaw.RadialCavityRecursion
import LocalLaw.FiniteBallCover
import LocalLaw.DeficientGraphIso

/-!
# Actual homogeneous cavity balls

Distance from the center is preserved by the induced ball. Interior degrees
are inherited because all neighbors remain inside; boundary tree vertices
have only their unique parent. This supplies the actual graph hypotheses
for the radial inverse-column proof.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance homogeneousCavityBallDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} (G : SimpleGraph V) (root : V) (r : ℕ)

def cavityBallRoot : graphBallVertices G root r := ⟨root, center_mem_graphBall G root r⟩

theorem graphBall_center_distance (v : graphBallVertices G root r) :
    (graphBall G root r).dist v (cavityBallRoot G root r) = G.dist v.val root := by
  let D := ballHeightParentData G root r
  obtain ⟨p, hp⟩ := D.walk_to_root v
  have hle : D.tree ≤ graphBall G root r := D.tree_le _ (ballHeightParentData_parent_adj G root r)
  have hupper := SimpleGraph.dist_le (p.mapLe hle)
  have hheight : D.height v = G.dist v.val root := by
    change (G.edist root v.val).toNat = G.dist v.val root
    rw [SimpleGraph.edist_comm]
    rfl
  have hup : (graphBall G root r).dist v (cavityBallRoot G root r) ≤ G.dist v.val root := by
    simpa only [SimpleGraph.Walk.mapLe, SimpleGraph.Walk.length_map, hp, hheight] using hupper
  obtain ⟨q, hq⟩ := (graphBall_connected G root r).exists_walk_length_eq_dist v (cavityBallRoot G root r)
  have hlo := SimpleGraph.dist_le (q.map (SimpleGraph.Embedding.induce (G := G) (graphBallVertices G root r)).toHom)
  simp only [SimpleGraph.Walk.length_map, hq] at hlo
  exact le_antisymm hup hlo

theorem graphBall_center_edist (v : graphBallVertices G root r) :
    G.edist root v.val = ((graphBall G root r).dist v (cavityBallRoot G root r) : ℕ∞) := by
  rw [graphBall_center_distance]
  have hh := ballVertexHeight_coe G root r v
  change ((G.edist root v.val).toNat : ℕ∞) = G.edist root v.val at hh
  simpa only [SimpleGraph.dist, SimpleGraph.edist_comm] using hh.symm

theorem graphBall_center_distance_le (v : graphBallVertices G root r) :
    (graphBall G root r).dist v (cavityBallRoot G root r) ≤ r := by
  apply ENat.coe_le_coe.mp
  rw [← graphBall_center_edist]
  exact v.property

section Finite
variable [Fintype V] [DecidableEq V]

theorem graphBall_interior_degree (v : graphBallVertices G root r)
    (hint : (graphBall G root r).dist v (cavityBallRoot G root r) < r) :
    (graphBall G root r).degree v = G.degree v.val := by
  apply SimpleGraph.degree_induce_of_neighborSet_subset
  intro w hw
  change G.edist root w ≤ (r : ℕ∞)
  calc
    _ ≤ G.edist root v.val + G.edist v.val w := G.edist_triangle
    _ = (((graphBall G root r).dist v (cavityBallRoot G root r) + 1 : ℕ) : ℕ∞) := by
      rw [graphBall_center_edist, SimpleGraph.edist_eq_one_iff_adj.mpr hw, Nat.cast_add, Nat.cast_one]
    _ ≤ _ := by exact_mod_cast hint

theorem tree_ball_boundary_degree (hTree : (graphBall G root r).IsTree)
    (v : graphBallVertices G root r)
    (hboundary : (graphBall G root r).dist v (cavityBallRoot G root r) = r) :
    (graphBall G root r).degree v = if v = cavityBallRoot G root r then 0 else 1 := by
  let H := graphBall G root r
  let o := cavityBallRoot G root r
  change H.dist v o = r at hboundary
  by_cases hv : v = o
  · have hr : r = 0 := by rw [hv, H.dist_self] at hboundary; exact hboundary.symm
    have hset : H.neighborFinset v = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro w hw
      have hw0 : H.dist w o = 0 := by
        have hh := graphBall_center_distance_le G root r w
        change H.dist w o ≤ r at hh
        omega
      have hwo : w = o := hTree.isConnected.dist_eq_zero_iff.mp hw0
      exact ((H.mem_neighborFinset v w).mp hw).ne (hv.trans hwo.symm)
    rw [if_pos hv]
    change H.degree v = 0
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hset, Finset.card_empty]
  · obtain ⟨p, hvp, hp, hfar⟩ := forest_parent_distance hTree.IsAcyclic o v
      (hTree.isConnected.preconnected v o) hv
    have hset : H.neighborFinset v = {p} := by
      ext w
      simp only [H.mem_neighborFinset, Finset.mem_singleton]
      constructor
      · intro hvw
        by_cases hwp : w = p
        · exact hwp
        · exfalso
          have hdist := hfar w hvw hwp
          change H.dist w o = H.dist v o + 1 at hdist
          have hcap := graphBall_center_distance_le G root r w
          change H.dist w o ≤ r at hcap
          omega
      · intro hw
        simpa only [hw] using hvp
    rw [if_neg hv]
    change H.degree v = 1
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hset, Finset.card_singleton]

end Finite

namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

/-- An actual saturated one-root-deficit tree ball has exactly the finite
cavity recursion at its center, for every physical boundary q. -/
theorem homogeneous_cavity_ball_diagonal (g : DeficientGraph V d) (hd : 3 ≤ d)
    (root : V) (r : ℕ) (hTree : (graphBall g.graph root r).IsTree)
    (hdeficit : ∀ v ∈ graphBallVertices g.graph root r,
      g.deficit v = if v = root then 1 else 0)
    (hsaturated : ∀ v ∈ graphBallVertices g.graph root r, g.graph.degree v + g.deficit v = d)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    (g.restrict (graphBallVertices g.graph root r)).extensionGreen q z
      (cavityBallRoot g.graph root r) (cavityBallRoot g.graph root r) = cavityIterate z q (r + 1) := by
  let M := g.restrict (graphBallVertices g.graph root r)
  let o := cavityBallRoot g.graph root r
  have hdef : ∀ v, M.deficit v = if v = o then 1 else 0 := by
    intro v
    change g.deficit v.val = _
    rw [hdeficit v.val v.property]
    simp only [o, cavityBallRoot, Subtype.ext_iff]
  have hdegree : ∀ v, M.graph.degree v = if M.graph.dist v o < r then
      (if v = o then d - 1 else d) else (if v = o then 0 else 1) := by
    intro v
    by_cases hint : M.graph.dist v o < r
    · rw [if_pos hint]
      change (graphBall g.graph root r).degree v = _
      rw [graphBall_interior_degree g.graph root r v hint]
      have hh := hsaturated v.val v.property
      have hδ := hdef v
      change g.deficit v.val = _ at hδ
      by_cases hv : v = o
      · rw [if_pos hv] at hδ ⊢
        omega
      · rw [if_neg hv] at hδ ⊢
        omega
    · rw [if_neg hint]
      exact tree_ball_boundary_degree g.graph root r hTree v
        (by
          have hh := graphBall_center_distance_le g.graph root r v
          change M.graph.dist v o ≤ r at hh
          change M.graph.dist v o = r
          omega)
  exact M.homogeneous_tree_cavity_diagonal hd o r hTree
    (graphBall_center_distance_le g.graph root r) hdef hdegree q z hz hq

theorem homogeneous_cavity_P_diagonal (g : DeficientGraph V d) (hd : 3 ≤ d)
    (root : V) (r : ℕ) (hTree : (graphBall g.graph root r).IsTree)
    (hdeficit : ∀ v ∈ graphBallVertices g.graph root r,
      g.deficit v = if v = root then 1 else 0)
    (hsaturated : ∀ v ∈ graphBallVertices g.graph root r, g.graph.degree v + g.deficit v = d)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    g.P r z q root root = cavityIterate z q (r + 1) := by
  have hh := g.homogeneous_cavity_ball_diagonal hd root r hTree hdeficit hsaturated q z hz hq
  let φ : pairBallGraph g.graph root root r ≃g graphBall g.graph root r :=
    { toFun := fun v => ⟨v.val, v.property.elim id id⟩
      invFun := fun v => ⟨v.val, Or.inl v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  have hiso := (g.restrict (graphBallVertices g.graph root r)).extensionGreen_iso
    (g.restrict (pairBallVertices g.graph root root r)) φ (fun _ => rfl) q z
  have hentry := congrFun (congrFun hiso (pairBallLeft g.graph root root r)) (pairBallRight g.graph root root r)
  exact hentry.symm.trans hh

end DeficientGraph
end LocalLaw
