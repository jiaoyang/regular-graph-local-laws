import LocalLaw.TreeKernelConvolution
import LocalLaw.BallCycleWitness

/-!
# Radius-sensitive actual tree boundary stability

The perturbation budget depends on the diameter rather than the number of
vertices. Induced graph balls have diameter at most twice their literal
radius, as proved by their actual shortest-distance parent walks.
-/

open scoped BigOperators Matrix
namespace LocalLaw
noncomputable section
local instance treeRadiusDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section FiniteTree
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Actual finite-tree version of the boundary-kernel stability estimate.
The kernel, convolution, nonsingularity and diameter estimates are proved;
only the explicit smallness of the perturbed boundary weight is required. -/
theorem fullTreeGreen_boundary_stability_of_diameter (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ v, G.degree v ≤ d) (Dcap : ℝ)
    (hdiam : ∀ a b, (G.dist a b : ℝ) ≤ Dcap) (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (small : 3 * (1 + Dcap) * ‖q - semicircleRoot z‖ ≤ 1 / 2) (i j : V) :
    ‖fullTreeGreen G d q z i j - fullTreeGreen G d (semicircleRoot z) z i j‖ ≤
        12 * ‖q - semicircleRoot z‖ * (1 + G.dist i j) *
          (‖semicircleRoot z‖ / Real.sqrt ((d : ℝ) - 1)) ^ G.dist i j ∧
      ‖fullTreeGreen G d q z i j‖ ≤
        4 * (‖semicircleRoot z‖ / Real.sqrt ((d : ℝ) - 1)) ^ G.dist i j := by
  let m := semicircleRoot z
  let t := ‖m‖ / Real.sqrt ((d : ℝ) - 1)
  let K := fun a b => t ^ G.dist a b
  let B := fun a b => (1 + (G.dist a b : ℝ)) * K a b
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hkpos : 0 < (d : ℝ) - 1 := by linarith
  have hs : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr hkpos
  have hmne : m ≠ 0 := cavity_root_ne_zero (semicircleRoot_equation z)
  have ht : 0 < t := div_pos (norm_pos_iff.mpr hmne) hs
  have htmax : t ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹ := by
    rw [← one_div]
    exact div_le_div_of_nonneg_right (semicircleRoot_norm_le_one z) hs.le
  have hD : ∀ v, 0 ≤ treeBoundaryWeight G d v := by
    intro v
    exact div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr (hdeg v))) hkpos.le
  have hunitq := boundaryMatrix_isUnit (normalizedAdjacency G d) (normalizedAdjacency_isHermitian G d)
    (treeBoundaryWeight G d) hD q z hz hq
  have hunitm := boundaryMatrix_isUnit (normalizedAdjacency G d) (normalizedAdjacency_isHermitian G d)
    (treeBoundaryWeight G d) hD m z hz (semicircleRoot_im_pos hz).le
  have hreference : ∀ a b,
      ‖boundaryGreen (normalizedAdjacency G d) (Matrix.diagonal (fun v => (treeBoundaryWeight G d v : ℂ))) m z a b‖ ≤
        2 * K a b := by
    intro a b
    change ‖fullTreeGreen G d m z a b‖ ≤ 2 * K a b
    rw [fullTreeGreen_eq_reference G d a,
      forestReference_full_norm_kernel G hG d hd hdeg a z hz a b]
    exact mul_le_mul_of_nonneg_right (kestenMcKayTransform_norm_le_two d hd z hz) (pow_nonneg ht.le _)
  have hcompanion : ∀ a b, B a b ≤ (1 + Dcap) * K a b := by
    intro a b
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg ht.le _)
    exact add_le_add_left (hdiam a b) 1
  have hconvolution : ∀ a b, (∑ x, treeBoundaryWeight G d x * K a x * K x b) ≤ (3 / 2 : ℝ) * B a b := by
    intro a b
    have hh := tree_boundary_convolution G hG d hd hdeg t ht.le htmax a b
    convert hh using 1
    dsimp [B, K]
    ring
  have hsmall : ‖q - m‖ * 2 * (3 / 2 : ℝ) * (1 + Dcap) ≤ 1 / 2 := by
    convert small using 1
    dsimp [m]
    ring
  have hh := boundary_kernel_stability (normalizedAdjacency G d) (treeBoundaryWeight G d)
    q m z hunitq hunitm K B 2 (3 / 2) (1 + Dcap) hD
    (fun a b => pow_nonneg ht.le _) (fun a b => mul_pos (by positivity) (pow_pos ht _))
    (by norm_num) (by norm_num) (by
      have hh : 0 ≤ Dcap := (Nat.cast_nonneg (G.dist i j)).trans (hdiam i j)
      linarith) hreference hcompanion hconvolution hsmall i j
  constructor
  · convert hh.1 using 1
    dsimp [B, K, t, m]
    ring
  · simpa only [K, t, m, show (2 : ℝ) * 2 = 4 by norm_num] using hh.2

/-- Actual two-weight tree boundary Lipschitz estimate. Its decay kernel and
all inverse/convolution requirements are consequences of the tree geometry. -/
theorem fullTreeGreen_two_weight_lipschitz_of_diameter (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ v, G.degree v ≤ d) (Dcap : ℝ)
    (hdiam : ∀ a b, (G.dist a b : ℝ) ≤ Dcap) (z q v : ℂ) (hz : 0 < z.im)
    (hq : 0 ≤ q.im) (hv : 0 ≤ v.im)
    (smallq : 3 * (1 + Dcap) * ‖q - semicircleRoot z‖ ≤ 1 / 2)
    (smallv : 3 * (1 + Dcap) * ‖v - semicircleRoot z‖ ≤ 1 / 2) (i j : V) :
    ‖fullTreeGreen G d q z i j - fullTreeGreen G d v z i j‖ ≤
      24 * (1 + G.dist i j) *
        (‖semicircleRoot z‖ / Real.sqrt ((d : ℝ) - 1)) ^ G.dist i j * dist q v := by
  let t := ‖semicircleRoot z‖ / Real.sqrt ((d : ℝ) - 1)
  let K := fun a b => t ^ G.dist a b
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hkpos : 0 < (d : ℝ) - 1 := by linarith
  have hs : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr hkpos
  have ht : 0 ≤ t := div_nonneg (norm_nonneg _) hs.le
  have htmax : t ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹ := by
    rw [← one_div]
    exact div_le_div_of_nonneg_right (semicircleRoot_norm_le_one z) hs.le
  have hD : ∀ x, 0 ≤ treeBoundaryWeight G d x := by
    intro x
    exact div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr (hdeg x))) hkpos.le
  have hunitq := boundaryMatrix_isUnit (normalizedAdjacency G d) (normalizedAdjacency_isHermitian G d)
    (treeBoundaryWeight G d) hD q z hz hq
  have hunitv := boundaryMatrix_isUnit (normalizedAdjacency G d) (normalizedAdjacency_isHermitian G d)
    (treeBoundaryWeight G d) hD v z hz hv
  have hqbound : ∀ a b, ‖fullTreeGreen G d q z a b‖ ≤ 4 * K a b :=
    fun a b => (fullTreeGreen_boundary_stability_of_diameter G hG d hd hdeg Dcap hdiam z q hz hq smallq a b).2
  have hvbound : ∀ a b, ‖fullTreeGreen G d v z a b‖ ≤ 4 * K a b :=
    fun a b => (fullTreeGreen_boundary_stability_of_diameter G hG d hd hdeg Dcap hdiam z v hz hv smallv a b).2
  have hproduct := diagonal_kernel_product_bound (fullTreeGreen G d q z) (fullTreeGreen G d v z)
    (treeBoundaryWeight G d) K K 4 4 hD (fun a b => pow_nonneg ht _) (by norm_num) (by norm_num)
    hqbound hvbound i j ((3 / 2 : ℝ) * (1 + G.dist i j) * K i j)
    (tree_boundary_convolution G hG d hd hdeg t ht htmax i j)
  have hid := congrArg (fun M : Matrix V V ℂ => M i j)
    (boundaryGreen_sub (normalizedAdjacency G d) (treeBoundaryDiagonal G d) q v z hunitq hunitv)
  change fullTreeGreen G d q z i j - fullTreeGreen G d v z i j =
    (q - v) * (fullTreeGreen G d q z * treeBoundaryDiagonal G d * fullTreeGreen G d v z) i j at hid
  rw [hid, norm_mul]
  calc
    _ ≤ ‖q - v‖ * (4 * 4 * ((3 / 2 : ℝ) * (1 + G.dist i j) * K i j)) :=
      mul_le_mul_of_nonneg_left hproduct (norm_nonneg _)
    _ = _ := by rw [dist_eq_norm]; dsimp [K, t]; ring

omit [Fintype V] [DecidableEq V] in
/-- The actual induced ball has intrinsic diameter at most twice its radius,
including cyclic balls. Its distance-decreasing parent walks stay inside it. -/
theorem graphBall_distance_le_twice_radius (o : V) (R : ℕ)
    (a b : graphBallVertices G o R) : (graphBall G o R).dist a b ≤ 2 * R := by
  let D := ballHeightParentData G o R
  have hle : D.tree ≤ graphBall G o R :=
    D.tree_le _ (ballHeightParentData_parent_adj G o R)
  obtain ⟨pa, hpa⟩ := D.walk_to_root a
  obtain ⟨pb, hpb⟩ := D.walk_to_root b
  let p := (pa.mapLe hle).append (pb.mapLe hle).reverse
  have hplen : p.length = D.height a + D.height b := by
    simp only [p, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
      SimpleGraph.Walk.mapLe, SimpleGraph.Walk.length_map, hpa, hpb]
  have ha : D.height a ≤ R := ballVertexHeight_le G o R a
  have hb : D.height b ≤ R := ballVertexHeight_le G o R b
  exact (SimpleGraph.dist_le p).trans (by rw [hplen]; omega)

/-- Boundary stability on an actual acyclic induced ball, with smallness
proportional to its radius rather than its number of vertices. -/
theorem graphBall_boundary_stability (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ v, G.degree v ≤ d) (o : V) (R : ℕ) (hball : (graphBall G o R).IsAcyclic)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (small : 3 * (1 + 2 * (R : ℝ)) * ‖q - semicircleRoot z‖ ≤ 1 / 2)
    (i j : graphBallVertices G o R) :
    ‖fullTreeGreen (graphBall G o R) d q z i j -
        fullTreeGreen (graphBall G o R) d (semicircleRoot z) z i j‖ ≤
      12 * ‖q - semicircleRoot z‖ * (1 + (graphBall G o R).dist i j) *
        (‖semicircleRoot z‖ / Real.sqrt ((d : ℝ) - 1)) ^ (graphBall G o R).dist i j ∧
      ‖fullTreeGreen (graphBall G o R) d q z i j‖ ≤
        4 * (‖semicircleRoot z‖ / Real.sqrt ((d : ℝ) - 1)) ^ (graphBall G o R).dist i j := by
  have hdegree : ∀ v : graphBallVertices G o R, (graphBall G o R).degree v ≤ d := by
    intro v
    exact (induced_degree_le G (graphBallVertices G o R) v).trans (hdeg v.val)
  apply fullTreeGreen_boundary_stability_of_diameter (graphBall G o R)
    ⟨graphBall_connected G o R, hball⟩ d hd hdegree (2 * (R : ℝ)) _ z q hz hq small i j
  intro a b
  exact_mod_cast graphBall_distance_le_twice_radius G o R a b

/-- Two actual boundary weights on an acyclic ball inherit the radius-scale
Lipschitz estimate, with no kernel or convolution assumption. -/
theorem graphBall_two_weight_lipschitz (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ v, G.degree v ≤ d) (o : V) (R : ℕ) (hball : (graphBall G o R).IsAcyclic)
    (z q v : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (hv : 0 ≤ v.im)
    (smallq : 3 * (1 + 2 * (R : ℝ)) * ‖q - semicircleRoot z‖ ≤ 1 / 2)
    (smallv : 3 * (1 + 2 * (R : ℝ)) * ‖v - semicircleRoot z‖ ≤ 1 / 2)
    (i j : graphBallVertices G o R) :
    ‖fullTreeGreen (graphBall G o R) d q z i j - fullTreeGreen (graphBall G o R) d v z i j‖ ≤
      24 * (1 + (graphBall G o R).dist i j) *
        (‖semicircleRoot z‖ / Real.sqrt ((d : ℝ) - 1)) ^ (graphBall G o R).dist i j * dist q v := by
  have hdegree : ∀ x : graphBallVertices G o R, (graphBall G o R).degree x ≤ d := by
    intro x
    exact (induced_degree_le G (graphBallVertices G o R) x).trans (hdeg x.val)
  apply fullTreeGreen_two_weight_lipschitz_of_diameter (graphBall G o R)
    ⟨graphBall_connected G o R, hball⟩ d hd hdegree (2 * (R : ℝ)) _ z q v hz hq hv smallq smallv i j
  intro a b
  exact_mod_cast graphBall_distance_le_twice_radius G o R a b

omit [Fintype V] [DecidableEq V] in
/-- Connected subgraphs of a forest preserve intrinsic distance. The mapped
shortest path is the unique simple path in the ambient forest. -/
theorem acyclic_embedding_distance_eq {W : Type*} {H : SimpleGraph W}
    (hG : G.Connected) (hH : H.IsAcyclic) (e : G ↪g H) (a b : V) :
    G.dist a b = H.dist (e a) (e b) := by
  obtain ⟨p, hp, hlen⟩ := (hG.preconnected a b).exists_path_of_dist
  have hh := acyclic_path_length_eq_dist hH (p.map e.toHom) (SimpleGraph.Walk.map_isPath_of_injective e.injective hp)
  simpa only [SimpleGraph.Walk.length_map, hlen] using hh

omit [Fintype V] [DecidableEq V] in
/-- Every connected induced subgraph inside an acyclic radius-R ball has
intrinsic diameter at most 2R, regardless of its number of vertices. -/
theorem induced_subtree_ball_diameter (o : V) (R : ℕ) (S : Set V)
    (hS : S ⊆ graphBallVertices G o R) (hconn : (G.induce S).Connected)
    (hball : (graphBall G o R).IsAcyclic) (a b : S) :
    (G.induce S).dist a b ≤ 2 * R := by
  have hh := acyclic_embedding_distance_eq (G.induce S) hconn hball
    (G.induceHomOfLE hS) a b
  rw [hh]
  exact graphBall_distance_le_twice_radius G o R _ _

end FiniteTree
end
end LocalLaw
