import LocalLaw.TreeReferenceKernel
import LocalLaw.ReferenceBounds

/-!
# Exact finite-tree boundary mass

Unique parents and finite neighbor-sum cancellation give the exact weighted
boundary mass. The genuine finite reference kernels then give weighted L2
bounds, with no Ward or convolution estimate assumed.
-/

open scoped BigOperators

namespace LocalLaw

noncomputable section
local instance treeMassDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section FiniteTree
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- The squared free-tree edge decay, with distance directed toward the root. -/
def treeFlowWeight (root : V) (k : ℝ) (v : V) : ℝ := (k⁻¹) ^ G.dist v root

omit [Fintype V] [DecidableEq V] in
@[simp] theorem treeFlowWeight_root (root : V) (k : ℝ) :
    treeFlowWeight G root k root = 1 := by simp [treeFlowWeight, G.dist_self]

omit [Fintype V] [DecidableEq V] in
theorem treeFlowWeight_nonneg (root : V) (k : ℝ) (hk : 0 ≤ k) (v : V) :
    0 ≤ treeFlowWeight G root k v := pow_nonneg (inv_nonneg.mpr hk) _

/-- The real geometric neighbor sum is inherited from the explicitly
verified forest kernel, using connectedness only to remove its component guard. -/
theorem tree_geometric_neighbor_sum (hG : G.IsTree) (root v parent : V) (t : ℝ)
    (hvp : G.Adj v parent) (hp : G.dist parent root + 1 = G.dist v root)
    (hfar : ∀ w, G.Adj v w → w ≠ parent → G.dist w root = G.dist v root + 1) :
    (∑ w ∈ G.neighborFinset v, t ^ G.dist w root) =
      ((G.degree v : ℝ) - 1) * t ^ (G.dist parent root + 2) + t ^ G.dist parent root := by
  have hr : ∀ w, G.Reachable w root := fun w => hG.isConnected.preconnected w root
  have hh := forestKernelColumn_neighbor_sum G root v parent 1 (t : ℂ) (hr v) hvp hp hfar
  simp only [forestKernelColumn, if_pos (hr _), one_mul, mul_one] at hh
  exact_mod_cast hh

/-- Exact local flow equation: the unique parent contributes k times the
vertex weight and every child contributes its weight divided by k. -/
theorem tree_flow_neighbor_identity (hG : G.IsTree) (root : V) (k : ℝ)
    (hk : k ≠ 0) (v : V) :
    k * (∑ w ∈ G.neighborFinset v, treeFlowWeight G root k w) =
      ((G.degree v : ℝ) + (k ^ 2 - 1) * (if v = root then 0 else 1)) * treeFlowWeight G root k v := by
  by_cases hv : v = root
  · subst v
    have hs : (∑ w ∈ G.neighborFinset root, treeFlowWeight G root k w) =
        (G.degree root : ℝ) * k⁻¹ := by
      calc
        _ = ∑ _w ∈ G.neighborFinset root, k⁻¹ := by
          apply Finset.sum_congr rfl
          intro w hw
          have hadj := (G.mem_neighborFinset root w).mp hw
          simp only [treeFlowWeight, SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm, pow_one]
        _ = _ := by simp [nsmul_eq_mul]
    simp only [hs, treeFlowWeight_root, if_pos rfl, mul_zero, add_zero, mul_one]
    field_simp
  · obtain ⟨parent, hvp, hp, hfar⟩ := forest_parent_distance hG.IsAcyclic root v
      (hG.isConnected.preconnected v root) hv
    rw [show (∑ w ∈ G.neighborFinset v, treeFlowWeight G root k w) =
      ∑ w ∈ G.neighborFinset v, (k⁻¹) ^ G.dist w root from rfl,
      tree_geometric_neighbor_sum G hG root v parent k⁻¹ hvp hp hfar]
    simp only [if_neg hv, mul_one, treeFlowWeight, ← hp]
    simp only [pow_add, pow_one]
    field_simp
    ring

omit [DecidableEq V] in
/-- Finite symmetric adjacency swaps the two neighbor sums exactly. -/
theorem sum_neighbor_sum_eq_degree_weight (f : V → ℝ) :
    (∑ v, ∑ w ∈ G.neighborFinset v, f w) = ∑ v, (G.degree v : ℝ) * f v := by
  calc
    _ = ∑ v, ∑ w : V, if G.Adj v w then f w else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [G.neighborFinset_eq_filter, Finset.sum_filter]
    _ = ∑ w, ∑ v : V, if G.Adj v w then f w else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      simp_rw [G.adj_comm]
      rw [← Finset.sum_filter, ← G.neighborFinset_eq_filter]
      simp [nsmul_eq_mul]

/-- The weighted degree sum is d times the weighted nonroot sum. -/
theorem tree_flow_degree_identity (hG : G.IsTree) (root : V) (k : ℝ)
    (hk : k ≠ 0) (hkone : k ≠ 1) :
    (∑ v, (G.degree v : ℝ) * treeFlowWeight G root k v) =
      (k + 1) * (∑ v, if v = root then 0 else treeFlowWeight G root k v) := by
  have hh := congrArg (fun f : V → ℝ => ∑ v, f v)
    (funext (tree_flow_neighbor_identity G hG root k hk))
  simp only at hh
  rw [← Finset.mul_sum, sum_neighbor_sum_eq_degree_weight] at hh
  have hrhs : (∑ v, ((G.degree v : ℝ) + (k ^ 2 - 1) * (if v = root then 0 else 1)) *
      treeFlowWeight G root k v) =
      (∑ v, (G.degree v : ℝ) * treeFlowWeight G root k v) +
        (k ^ 2 - 1) * (∑ v, if v = root then 0 else treeFlowWeight G root k v) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v = root <;> simp [hv]
    ring
  rw [hrhs] at hh
  have hcancel : (k - 1) * ((∑ v, (G.degree v : ℝ) * treeFlowWeight G root k v) -
      (k + 1) * (∑ v, if v = root then 0 else treeFlowWeight G root k v)) = 0 := by
    linear_combination hh
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcancel).resolve_left (sub_ne_zero.mpr hkone))

/-- Exact boundary mass for any root deficit b, including b=1 cavities and
b=0 full trees. The algebraic identity itself needs no degree upper bound. -/
theorem tree_boundary_mass (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d) (root : V) (b : ℕ) :
    (∑ v, forestBoundaryCoefficient G d root b v * treeFlowWeight G root ((d : ℝ) - 1) v) =
      ((d : ℝ) - (b : ℝ)) / ((d : ℝ) - 1) := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hdegree := tree_flow_degree_identity G hG root ((d : ℝ) - 1) (by linarith) (by linarith)
  have hroot : (∑ v, if v = root then treeFlowWeight G root ((d : ℝ) - 1) v else 0) = 1 := by simp
  have hsplit : (∑ v, treeFlowWeight G root ((d : ℝ) - 1) v) =
      1 + (∑ v, if v = root then 0 else treeFlowWeight G root ((d : ℝ) - 1) v) := by
    rw [← hroot, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v = root <;> simp [hv]
  have hsum : (∑ v, ((d : ℝ) - (if v = root then (b : ℝ) else 0) - (G.degree v : ℝ)) *
      treeFlowWeight G root ((d : ℝ) - 1) v) = (d : ℝ) - (b : ℝ) := by
    have hbroot : (∑ v, (if v = root then (b : ℝ) else 0) * treeFlowWeight G root ((d : ℝ) - 1) v) = b := by simp
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hbroot, hsplit, hdegree]
    ring
  simp only [forestBoundaryCoefficient, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [hsum]

@[simp] theorem tree_cavity_boundary_mass (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d) (root : V) :
    (∑ v, forestBoundaryCoefficient G d root 1 v * treeFlowWeight G root ((d : ℝ) - 1) v) = 1 := by
  rw [tree_boundary_mass G hG d hd root 1]
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  norm_num only [Nat.cast_one]
  exact div_self (by linarith)

/-- Unnormalized form: the missing degrees carry total mass d-b. -/
theorem tree_missing_degree_mass (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (root : V) (b : ℕ) :
    (∑ v, ((d : ℝ) - (if v = root then (b : ℝ) else 0) - (G.degree v : ℝ)) *
      treeFlowWeight G root ((d : ℝ) - 1) v) = (d : ℝ) - (b : ℝ) := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hk : (d : ℝ) - 1 ≠ 0 := by linarith
  have hh := tree_boundary_mass G hG d hd root b
  simp only [forestBoundaryCoefficient, div_mul_eq_mul_div, ← Finset.sum_div] at hh
  exact (div_left_inj' hk).mp hh

/-- Exact squared edge normalization. -/
theorem treeEdgeWeight_norm_sq (d : ℕ) (hd : 3 ≤ d) :
    ‖treeEdgeWeight d‖ ^ 2 = 1 / ((d : ℝ) - 1) := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hs : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  simp only [treeEdgeWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hs), inv_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ d - 1), one_div]

omit [Fintype V] [DecidableEq V] in
/-- Pointwise squared physical kernel decay is bounded by the free-tree flow. -/
theorem tree_kernel_norm_sq_le (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (root : V) (c m : ℂ) (hm : ‖m‖ ≤ 1) (v : V) :
    ‖forestKernelColumn G root c (-m * treeEdgeWeight d) v‖ ^ 2 ≤
      ‖c‖ ^ 2 * treeFlowWeight G root ((d : ℝ) - 1) v := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hkpos : 0 < (d : ℝ) - 1 := by linarith
  have hbase : ‖-m * treeEdgeWeight d‖ ^ 2 ≤ ((d : ℝ) - 1)⁻¹ := by
    rw [norm_mul, norm_neg, mul_pow, treeEdgeWeight_norm_sq d hd, one_div]
    exact mul_le_of_le_one_left (inv_nonneg.mpr hkpos.le)
      (pow_le_one₀ (norm_nonneg _) hm)
  have hreach := hG.isConnected.preconnected v root
  rw [forestKernelColumn, if_pos hreach, norm_mul, mul_pow, norm_pow]
  rw [← pow_mul, Nat.mul_comm (G.dist v root) 2, pow_mul]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (sq_nonneg _) hbase (G.dist v root)) (sq_nonneg _)

/-- Exact finite-tree mass controls the actual boundary-weighted squared
kernel for every root coefficient c and every physical edge parameter. -/
theorem tree_kernel_boundary_l2_bound (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (root : V) (b : ℕ) (hdeg : ∀ v, G.degree v + (if v = root then b else 0) ≤ d)
    (c m : ℂ) (hm : ‖m‖ ≤ 1) :
    (∑ v, forestBoundaryCoefficient G d root b v *
      ‖forestKernelColumn G root c (-m * treeEdgeWeight d) v‖ ^ 2) ≤
        ‖c‖ ^ 2 * (((d : ℝ) - (b : ℝ)) / ((d : ℝ) - 1)) := by
  calc
    _ ≤ ∑ v, forestBoundaryCoefficient G d root b v *
        (‖c‖ ^ 2 * treeFlowWeight G root ((d : ℝ) - 1) v) := by
      apply Finset.sum_le_sum
      intro v _
      exact mul_le_mul_of_nonneg_left (tree_kernel_norm_sq_le G hG d hd root c m hm v)
        (forestBoundaryCoefficient_nonnegative G d hd root b hdeg v)
    _ = ‖c‖ ^ 2 * (∑ v, forestBoundaryCoefficient G d root b v *
        treeFlowWeight G root ((d : ℝ) - 1) v) := by rw [Finset.mul_sum]; congr 1; funext v; ring
    _ = _ := by rw [tree_boundary_mass G hG d hd root b]

/-- Genuine cavity inverse column has boundary-weighted L2 norm at most one.
The inverse formula and boundary flow are both proved on the actual tree. -/
theorem forestReference_cavity_weighted_l2 (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (root : V) (hdeg : ∀ v, G.degree v + (if v = root then 1 else 0) ≤ d)
    (m z : ℂ) (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im)
    (hmim : 0 ≤ m.im) (hmnorm : ‖m‖ ≤ 1) :
    (∑ v, forestBoundaryCoefficient G d root 1 v *
      ‖(forestReferenceMatrix G d root 1 m z)⁻¹ v root‖ ^ 2) ≤ 1 := by
  simp_rw [forestReference_cavity_column G hG.IsAcyclic d hd root hdeg m z hm hz hmim]
  have hh := tree_kernel_boundary_l2_bound G hG d hd root 1 hdeg m m hmnorm
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hid : ((d : ℝ) - (1 : ℕ)) / ((d : ℝ) - 1) = 1 := by
    norm_num only [Nat.cast_one]
    exact div_self (by linarith)
  rw [hid, mul_one] at hh
  exact hh.trans (pow_le_one₀ (norm_nonneg _) hmnorm)

/-- Genuine full-tree physical reference inverse has boundary-weighted L2
norm at most six, uniformly in its finite depth and shape. -/
theorem forestReference_full_weighted_l2 (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (root : V) (hdeg : ∀ v, G.degree v ≤ d) (z : ℂ) (hz : 0 < z.im) :
    (∑ v, forestBoundaryCoefficient G d root 0 v *
      ‖(forestReferenceMatrix G d root 0 (semicircleRoot z) z)⁻¹ v root‖ ^ 2) ≤ 6 := by
  simp_rw [forestReference_full_column G hG.IsAcyclic d hd root hdeg (semicircleRoot z)
    z (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le]
  have hdeg' : ∀ v, G.degree v + (if v = root then 0 else 0) ≤ d := by simpa using hdeg
  have hh := tree_kernel_boundary_l2_bound G hG d hd root 0 hdeg'
    (kestenMcKayTransform d (semicircleRoot z) z) (semicircleRoot z) (semicircleRoot_norm_le_one z)
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hkpos : 0 < (d : ℝ) - 1 := by linarith
  have hratio : (d : ℝ) / ((d : ℝ) - 1) ≤ 3 / 2 := (div_le_iff₀ hkpos).mpr (by linarith)
  have hp := kestenMcKayTransform_norm_le_two d hd z hz
  have hp2 : ‖kestenMcKayTransform d (semicircleRoot z) z‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (kestenMcKayTransform d (semicircleRoot z) z)]
  simp only [Nat.cast_zero, sub_zero] at hh
  exact hh.trans ((mul_le_mul hp2 hratio (by positivity) (by norm_num)).trans_eq (by norm_num))

end FiniteTree
end
end LocalLaw
