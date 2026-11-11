import LocalLaw.RootDeficitTreeKernel
import LocalLaw.DeficientGraphModel

/-!
# Finite actual good threshold one

For connected finite source graphs with total deficit plus excess at most one,
the actual finite extension inverse has uniform entry, imaginary and diagonal
bounds. The three possible geometries are proved from the numeric budget:
zero-deficit trees, one-root-deficit trees, and zero-deficit unicyclic graphs.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance goodOneDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A natural-valued function with total mass at most one is either zero or
one at a unique distinguished vertex and zero elsewhere. -/
theorem deficit_sum_le_one_shape {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℕ) (hbudget : (∑ v, f v) ≤ 1) :
    (∀ v, f v = 0) ∨ ∃ root, ∀ v, f v = if v = root then 1 else 0 := by
  classical
  by_cases hzero : ∀ v, f v = 0
  · exact Or.inl hzero
  · right
    obtain ⟨root, hroot⟩ : ∃ v, f v ≠ 0 := by simpa only [not_forall] using hzero
    have hrootle : f root ≤ 1 :=
      (Finset.single_le_sum (fun v (_ : v ∈ Finset.univ) => Nat.zero_le (f v)) (Finset.mem_univ root)).trans hbudget
    have hrootone : f root = 1 := by omega
    have herase := Finset.sum_erase_add Finset.univ f (Finset.mem_univ root)
    rw [hrootone] at herase
    have hzerorest : (∑ v ∈ Finset.univ.erase root, f v) = 0 := by omega
    refine ⟨root, ?_⟩
    intro v
    by_cases hv : v = root
    · simpa only [hv, if_pos rfl] using hrootone
    · rw [if_neg hv]
      have hh := Finset.single_le_sum (fun v (_ : v ∈ Finset.univ.erase root) => Nat.zero_le (f v))
        (Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩)
      rw [hzerorest] at hh
      omega

/-- Connectivity and excess zero identify an actual finite tree. -/
theorem connected_excess_zero_isTree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (hexcess : graphExcess G = 0) : G.IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hconn, ?_⟩
  have hh := connected_graph_excess_euler G hconn
  rw [hexcess, zero_add] at hh
  exact hh.symm

namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

/-- Exact zero-deficit identification of the actual source extension. -/
theorem extensionGreen_eq_full_of_zero_deficit (g : DeficientGraph V d)
    (hzero : ∀ v, g.deficit v = 0) (w z : ℂ) :
    g.extensionGreen w z = fullTreeGreen g.graph d w z := by
  unfold extensionGreen boundaryGreen fullTreeGreen boundaryDiagonal treeBoundaryDiagonal H
  congr 1
  apply congrArg (fun D => boundaryMatrix (normalizedAdjacency g.graph d) D w z)
  apply congrArg Matrix.diagonal
  funext v
  simp only [boundaryCoefficient, hzero, Nat.cast_zero, sub_zero, treeBoundaryWeight]

/-- Exact one-root-deficit identification, with no assumed finite model. -/
theorem extensionGreen_eq_root_deficit (g : DeficientGraph V d) (root : V)
    (hroot : ∀ v, g.deficit v = if v = root then 1 else 0) (w z : ℂ) :
    g.extensionGreen w z = (forestReferenceMatrix g.graph d root 1 w z)⁻¹ := by
  unfold extensionGreen boundaryGreen forestReferenceMatrix boundaryDiagonal H
  congr 1
  apply congrArg (fun D => boundaryMatrix (normalizedAdjacency g.graph d) D w z)
  apply congrArg Matrix.diagonal
  funext v
  by_cases hv : v = root <;> simp [boundaryCoefficient, forestBoundaryCoefficient, hroot, hv]

/-- The finite form of the good-threshold-one reference conclusions. -/
structure ReferenceOneBounds (g : DeficientGraph V d) (z : ℂ) : Prop where
  entry : ∀ i j, ‖g.extensionGreen (semicircleRoot z) z i j‖ ≤
    8 * ‖-semicircleRoot z * treeEdgeWeight d‖ ^ g.graph.dist i j
  imaginary : ∀ i j, |(g.extensionGreen (semicircleRoot z) z i j).im| ≤
    192 * (kestenMcKayTransform d (semicircleRoot z) z).im
  diagonal : ∀ i, ‖kestenMcKayTransform d (semicircleRoot z) z‖ / 4 ≤
    ‖g.extensionGreen (semicircleRoot z) z i i‖

/-- Actual connected finite deficient graphs with total complexity at most
one have good reference bounds. No geometric classification is an input. -/
theorem finite_good_threshold_one (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hconn : g.graph.Connected) (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ 1)
    (z : ℂ) (hz : 0 < z.im) : ReferenceOneBounds g z := by
  let m := semicircleRoot z
  let p := kestenMcKayTransform d m z
  have hmim : 0 ≤ m.im := (semicircleRoot_im_pos hz).le
  have hpim : 0 ≤ p.im := (kestenMcKayTransform_im_pos d m z hz hmim).le
  have hsumle : (∑ v, g.deficit v) ≤ 1 := by omega
  rcases deficit_sum_le_one_shape g.deficit hsumle with hzero | ⟨root, hroot⟩
  · have hsum : (∑ v, g.deficit v) = 0 := by simp only [hzero, Finset.sum_const_zero]
    have hexcess : graphExcess g.graph = 0 ∨ graphExcess g.graph = 1 := by omega
    rcases hexcess with htree | hcycle
    · have hG := connected_excess_zero_isTree g.graph hconn htree
      have hfull := g.extensionGreen_eq_full_of_zero_deficit hzero m z
      let root : V := Classical.choice hconn.nonempty
      have hkernel : ∀ i j, fullTreeGreen g.graph d m z i j = p * (-m * treeEdgeWeight d) ^ g.graph.dist i j := by
        intro i j
        rw [fullTreeGreen_eq_reference g.graph d root]
        exact forestReference_full_kernel g.graph hG d hd g.degree_le root m z (semicircleRoot_equation z) hz hmim i j
      constructor
      · intro i j
        rw [hfull, hkernel, norm_mul]
        have hh := mul_le_mul_of_nonneg_right (kestenMcKayTransform_norm_le_two d hd z hz)
          (pow_nonneg (norm_nonneg (-m * treeEdgeWeight d)) (g.graph.dist i j))
        rw [norm_pow]
        exact hh.trans (by nlinarith [pow_nonneg (norm_nonneg (-m * treeEdgeWeight d)) (g.graph.dist i j)])
      · intro i j
        rw [hfull, fullTreeGreen_eq_reference g.graph d root]
        have hh := forestReference_full_im_bound g.graph hG d hd g.degree_le root z hz i j
        have hcomp := semicircleRoot_im_le_md d hd z hz
        linarith
      · intro i
        rw [hfull, hkernel, g.graph.dist_self, pow_zero, mul_one]
        exact (div_le_self (norm_nonneg p) (by norm_num : (1 : ℝ) ≤ 4))
    · have hfull := g.extensionGreen_eq_full_of_zero_deficit hzero m z
      constructor
      · intro i j
        rw [hfull]
        exact unicyclic_reference_entry_bound g.graph hconn hcycle d hd g.degree_le z hz i j
      · intro i j
        rw [hfull]
        exact unicyclic_reference_im_md_bound g.graph hconn hcycle d hd g.degree_le z hz i j
      · intro i
        rw [hfull]
        exact unicyclic_reference_diagonal_relative_lower g.graph hconn hcycle d hd g.degree_le z hz i
  · have hrootone : g.deficit root = 1 := by simp only [hroot, if_pos rfl, ite_true]
    have hsumpos : 1 ≤ ∑ v, g.deficit v := by
      simpa only [hrootone] using Finset.single_le_sum
        (fun v (_ : v ∈ Finset.univ) => Nat.zero_le (g.deficit v)) (Finset.mem_univ root)
    have hexcess : graphExcess g.graph = 0 := by omega
    have hG := connected_excess_zero_isTree g.graph hconn hexcess
    have hdeg : ∀ v, g.graph.degree v + (if v = root then 1 else 0) ≤ d := by
      intro v
      simpa only [hroot] using g.degree_deficit_le v
    have hmodel := g.extensionGreen_eq_root_deficit root hroot m z
    constructor
    · intro i j
      rw [hmodel]
      exact (root_deficit_tree_entry_bound g.graph hG d hd root hdeg z hz i j).trans
        (mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 8) (pow_nonneg (norm_nonneg _) _))
    · intro i j
      rw [hmodel]
      have hh := root_deficit_tree_im_bound g.graph hG d hd root hdeg z hz i j
      have hcomp := semicircleRoot_im_le_md d hd z hz
      linarith
    · intro i
      rw [hmodel]
      have hh := root_deficit_tree_diagonal_lower g.graph hG d hd root hdeg z hz i
      exact (by linarith [norm_nonneg p] : ‖p‖ / 4 ≤ ‖p‖ / 2).trans hh

/-- Public entry estimate with the actual source deficit convention. -/
theorem reference_one_entry_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hconn : g.graph.Connected) (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ 1)
    (z : ℂ) (hz : 0 < z.im) (i j : V) :
    ‖g.extensionGreen (semicircleRoot z) z i j‖ ≤
      8 * ‖-semicircleRoot z * treeEdgeWeight d‖ ^ g.graph.dist i j :=
  (g.finite_good_threshold_one hd hconn hbudget z hz).entry i j

/-- Public imaginary estimate in the paper's regular-tree normalization. -/
theorem reference_one_im_md_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hconn : g.graph.Connected) (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ 1)
    (z : ℂ) (hz : 0 < z.im) (i j : V) :
    |(g.extensionGreen (semicircleRoot z) z i j).im| ≤
      192 * (kestenMcKayTransform d (semicircleRoot z) z).im :=
  (g.finite_good_threshold_one hd hconn hbudget z hz).imaginary i j

theorem reference_one_diagonal_relative_lower (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hconn : g.graph.Connected) (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ 1)
    (z : ℂ) (hz : 0 < z.im) (i : V) :
    ‖kestenMcKayTransform d (semicircleRoot z) z‖ / 4 ≤ ‖g.extensionGreen (semicircleRoot z) z i i‖ :=
  (g.finite_good_threshold_one hd hconn hbudget z hz).diagonal i

/-- Concrete bounded-domain diagonal comparability for every actual graph
under the threshold-one deficit/excess budget. -/
theorem reference_one_diagonal_bounds (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hconn : g.graph.Connected) (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ 1)
    (z : ℂ) (hz : 0 < z.im) (B : ℝ) (hB : ‖z‖ ≤ B) (i : V) :
    1 / (4 * (B + 2)) ≤ ‖g.extensionGreen (semicircleRoot z) z i i‖ ∧
      ‖g.extensionGreen (semicircleRoot z) z i i‖ ≤ 8 := by
  constructor
  · have hh := div_le_div_of_nonneg_right (kestenMcKay_bounded_norm_lower d hd z hz B hB) (by norm_num : (0 : ℝ) ≤ 4)
    have hrate : (1 / (B + 2)) / 4 = 1 / (4 * (B + 2)) := by field_simp; ring
    rw [hrate] at hh
    exact hh.trans (g.reference_one_diagonal_relative_lower hd hconn hbudget z hz i)
  · simpa only [g.graph.dist_self, pow_zero, mul_one] using g.reference_one_entry_bound hd hconn hbudget z hz i i

end DeficientGraph
end
end LocalLaw
