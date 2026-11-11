import LocalLaw.CavityTreeFeedback
import LocalLaw.TreeRecursion

/-!
# Exact cavity recursion on an actual homogeneous finite tree

The proof verifies a radial inverse column on the actual vertex type. No
enumeration or isomorphism with a canonical tree, and no final matrix-entry
identity, is assumed.
-/

open scoped BigOperators Matrix
noncomputable section
namespace LocalLaw
local instance radialCavityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem cavityIterate_im_nonnegative (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (n : ℕ) :
    0 ≤ (cavityIterate z q n).im := by
  induction n with
  | zero => exact hq
  | succ n ih =>
    simp only [cavityIterate, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_nonneg (by simpa only [Complex.add_im] using add_nonneg hz.le ih)
      (Complex.normSq_nonneg _)

theorem cavityIterate_step_nonzero (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (n : ℕ) :
    z + cavityIterate z q n ≠ 0 := by
  have hh : 0 < (z + cavityIterate z q n).im := by
    rw [Complex.add_im]
    exact add_pos_of_pos_of_nonneg hz (cavityIterate_im_nonnegative z q hz hq n)
  exact fun h => by rw [h, Complex.zero_im] at hh; exact (lt_irrefl _ hh)

theorem cavityIterate_step_product (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (n : ℕ) :
    (z + cavityIterate z q n) * cavityIterate z q (n + 1) = -1 := by
  rw [cavityIterate, mul_neg, mul_inv_cancel₀ (cavityIterate_step_nonzero z q hz hq n)]

def radialCavityColumn (z q α : ℂ) (r : ℕ) : ℕ → ℂ
  | 0 => cavityIterate z q (r + 1)
  | h + 1 => -α * cavityIterate z q (r - h) * radialCavityColumn z q α r h

theorem radialCavityColumn_parent (z q α : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (r n : ℕ) (hn : n + 1 ≤ r) :
    (z + cavityIterate z q (r - (n + 1))) * radialCavityColumn z q α r (n + 1) =
      α * radialCavityColumn z q α r n := by
  have heq : r - n = (r - (n + 1)) + 1 := by omega
  rw [radialCavityColumn, heq]
  linear_combination -(α * radialCavityColumn z q α r n) *
    cavityIterate_step_product z q hz hq (r - (n + 1))

section FiniteTree
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

omit [DecidableEq V] in
theorem radial_root_neighbor_sum (root : V) (f : ℕ → ℂ) :
    (∑ w ∈ G.neighborFinset root, f (G.dist w root)) = (G.degree root : ℂ) * f 1 := by
  calc
    _ = ∑ _w ∈ G.neighborFinset root, f 1 := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset root w).mp hw).symm]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree]

theorem radial_nonroot_neighbor_sum (root v parent : V) (f : ℕ → ℂ)
    (hvp : G.Adj v parent)
    (hfar : ∀ w, G.Adj v w → w ≠ parent → G.dist w root = G.dist v root + 1) :
    (∑ w ∈ G.neighborFinset v, f (G.dist w root)) =
      ((G.degree v : ℂ) - 1) * f (G.dist v root + 1) + f (G.dist parent root) := by
  have hmem : parent ∈ G.neighborFinset v := (G.mem_neighborFinset v parent).mpr hvp
  have hcardNat := Finset.card_erase_add_one hmem
  have hcard : (((G.neighborFinset v).erase parent).card : ℂ) = (G.degree v : ℂ) - 1 := by
    have hh : (((G.neighborFinset v).erase parent).card : ℂ) + 1 = (G.degree v : ℂ) := by
      exact_mod_cast hcardNat
    linear_combination hh
  rw [← Finset.sum_erase_add (G.neighborFinset v) (fun w => f (G.dist w root)) hmem]
  have hsum : (∑ w ∈ (G.neighborFinset v).erase parent, f (G.dist w root)) =
      (((G.neighborFinset v).erase parent).card : ℂ) * f (G.dist v root + 1) := by
    calc
      _ = ∑ _w ∈ (G.neighborFinset v).erase parent, f (G.dist v root + 1) := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [hfar w ((G.mem_neighborFinset v w).mp (Finset.mem_of_mem_erase hw)) (Finset.mem_erase.mp hw).1]
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hsum, hcard]

def radialCavityMatrix (d : ℕ) (root : V) (r : ℕ) (q z : ℂ) : Matrix V V ℂ :=
  boundaryMatrix (normalizedAdjacency G d)
    (Matrix.diagonal (fun v => if G.dist v root = r then 1 else 0)) q z

theorem radialCavityMatrix_mulVec (d : ℕ) (root : V) (r : ℕ) (q z : ℂ) (f : V → ℂ) (v : V) :
    (radialCavityMatrix G d root r q z *ᵥ f) v =
      treeEdgeWeight d * (∑ w ∈ G.neighborFinset v, f w) - z * f v -
        q * (if G.dist v root = r then 1 else 0) * f v := by
  unfold radialCavityMatrix boundaryMatrix spectralMatrix
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
    Matrix.smul_mulVec_assoc]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal]
  rw [normalizedAdjacency_mulVec_neighbor]
  ring

theorem radialCavityMatrix_column (d : ℕ) (hd : 3 ≤ d) (root : V) (r : ℕ)
    (hG : G.IsTree) (hheight : ∀ v, G.dist v root ≤ r)
    (hdegree : ∀ v, G.degree v = if G.dist v root < r then
      (if v = root then d - 1 else d) else (if v = root then 0 else 1))
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    radialCavityMatrix G d root r q z *ᵥ
      (fun v => radialCavityColumn z q (treeEdgeWeight d) r (G.dist v root)) = Pi.single root 1 := by
  let α := treeEdgeWeight d
  let F := radialCavityColumn z q α r
  have hnorm : ((d : ℂ) - 1) * α ^ 2 = 1 := by
    dsimp only [α]
    rw [treeEdgeWeight_sq d hd]
    have hk : (d : ℂ) - 1 ≠ 0 := by
      have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
      exact_mod_cast (show (d : ℝ) - 1 ≠ 0 by linarith)
    field_simp
  funext v
  rw [radialCavityMatrix_mulVec]
  change α * (∑ w ∈ G.neighborFinset v, F (G.dist w root)) - z * F (G.dist v root) -
    q * (if G.dist v root = r then 1 else 0) * F (G.dist v root) = (Pi.single root (1 : ℂ) : V → ℂ) v
  by_cases hv : v = root
  · subst v
    rw [radial_root_neighbor_sum, G.dist_self]
    simp only [Pi.single_apply, if_pos rfl, ite_true]
    by_cases hr : r = 0
    · subst r
      have hd0 : G.degree root = 0 := by simpa only [G.dist_self, lt_self_iff_false, if_false, ite_true] using hdegree root
      rw [hd0]
      simp only [Nat.cast_zero, zero_mul, mul_zero, zero_sub, G.dist_self, if_pos rfl, ite_true, one_mul, mul_one]
      change -(z * cavityIterate z q 1) - q * cavityIterate z q 1 = 1
      have hstep := cavityIterate_step_product z q hz hq 0
      change (z + q) * cavityIterate z q 1 = -1 at hstep
      linear_combination -hstep
    · have hdeg : G.degree root = d - 1 := by
        simpa only [G.dist_self, if_pos (Nat.pos_of_ne_zero hr), ite_true] using hdegree root
      rw [hdeg, Nat.cast_sub (by omega : 1 ≤ d)]
      simp only [Nat.cast_one, if_neg (Ne.symm hr)]
      change α * (((d : ℂ) - 1) * (-α * cavityIterate z q r * cavityIterate z q (r + 1))) -
        z * cavityIterate z q (r + 1) - q * 0 * cavityIterate z q (r + 1) = 1
      linear_combination -(cavityIterate z q r * cavityIterate z q (r + 1)) * hnorm -
        cavityIterate_step_product z q hz hq r
  · rw [Pi.single_apply, if_neg hv]
    obtain ⟨parent, hvp, hp, hfar⟩ := forest_parent_distance hG.IsAcyclic root v (hG.isConnected.preconnected v root) hv
    rw [radial_nonroot_neighbor_sum G root v parent F hvp hfar]
    have hparent := radialCavityColumn_parent z q α hz hq r (G.dist parent root)
      (by rw [hp]; exact hheight v)
    change (z + cavityIterate z q (r - (G.dist parent root + 1))) * F (G.dist parent root + 1) =
      α * F (G.dist parent root) at hparent
    rw [hp] at hparent
    by_cases hboundary : G.dist v root = r
    · have hdeg : G.degree v = 1 := by
        simpa only [hboundary, lt_self_iff_false, if_false, if_neg hv] using hdegree v
      rw [hdeg]
      simp only [Nat.cast_one, sub_self, zero_mul, zero_add, if_pos hboundary, mul_one]
      rw [hboundary, Nat.sub_self] at hparent
      change (z + q) * F r = α * F (G.dist parent root) at hparent
      rw [hboundary]
      linear_combination -hparent
    · have hinterior : G.dist v root < r := lt_of_le_of_ne (hheight v) hboundary
      have hdeg : G.degree v = d := by simpa only [if_pos hinterior, if_neg hv] using hdegree v
      rw [hdeg, if_neg hboundary]
      have hchild : α * (((d : ℂ) - 1) * F (G.dist v root + 1)) =
          -cavityIterate z q (r - G.dist v root) * F (G.dist v root) := by
        change α * (((d : ℂ) - 1) * (-α * cavityIterate z q (r - G.dist v root) * F (G.dist v root))) = _
        linear_combination -(cavityIterate z q (r - G.dist v root) * F (G.dist v root)) * hnorm
      linear_combination -hparent + hchild

theorem radialCavityMatrix_inverse_root (d : ℕ) (hd : 3 ≤ d) (root : V) (r : ℕ)
    (hG : G.IsTree) (hheight : ∀ v, G.dist v root ≤ r)
    (hdegree : ∀ v, G.degree v = if G.dist v root < r then
      (if v = root then d - 1 else d) else (if v = root then 0 else 1))
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    (radialCavityMatrix G d root r q z)⁻¹ root root = cavityIterate z q (r + 1) := by
  have hunit : IsUnit (radialCavityMatrix G d root r q z) := by
    have hh := boundaryMatrix_isUnit (normalizedAdjacency G d) (normalizedAdjacency_isHermitian G d)
      (fun v => if G.dist v root = r then (1 : ℝ) else 0) (fun v => by dsimp only; split_ifs <;> norm_num)
      q z hz hq
    simpa only [radialCavityMatrix, apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using hh
  have hh := inverse_column_of_mulVec _ hunit _ root
    (radialCavityMatrix_column G d hd root r hG hheight hdegree q z hz hq) root
  simpa only [G.dist_self, radialCavityColumn] using hh

theorem homogeneous_forest_boundary_coefficient (d : ℕ) (hd : 3 ≤ d) (root : V) (r : ℕ)
    (hheight : ∀ v, G.dist v root ≤ r)
    (hdegree : ∀ v, G.degree v = if G.dist v root < r then
      (if v = root then d - 1 else d) else (if v = root then 0 else 1)) (v : V) :
    forestBoundaryCoefficient G d root 1 v = if G.dist v root = r then 1 else 0 := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hk : (d : ℝ) - 1 ≠ 0 := by linarith
  by_cases hb : G.dist v root = r
  · have hlt : ¬G.dist v root < r := by omega
    have hdeg : G.degree v = if v = root then 0 else 1 := by rw [hdegree v, if_neg hlt]
    unfold forestBoundaryCoefficient
    rw [hdeg, if_pos hb]
    by_cases hv : v = root
    · simp only [if_pos hv, Nat.cast_one, Nat.cast_zero]
      field_simp [hk]
    · simp only [if_neg hv, Nat.cast_one, Nat.cast_zero]
      field_simp [hk]
  · have hlt : G.dist v root < r := lt_of_le_of_ne (hheight v) hb
    have hdeg : G.degree v = if v = root then d - 1 else d := by rw [hdegree v, if_pos hlt]
    unfold forestBoundaryCoefficient
    rw [hdeg, if_neg hb]
    by_cases hv : v = root
    · simp only [if_pos hv, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one, Nat.cast_zero]
      ring
    · simp only [if_neg hv, Nat.cast_one, Nat.cast_zero]
      ring

end FiniteTree

namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

/-- The exact scalar recursion on an actual finite homogeneous cavity tree,
with its genuine source one-root deficit and normalized graph matrix. -/
theorem homogeneous_tree_cavity_diagonal (g : DeficientGraph V d) (hd : 3 ≤ d)
    (root : V) (r : ℕ) (hG : g.graph.IsTree) (hheight : ∀ v, g.graph.dist v root ≤ r)
    (hdeficit : ∀ v, g.deficit v = if v = root then 1 else 0)
    (hdegree : ∀ v, g.graph.degree v = if g.graph.dist v root < r then
      (if v = root then d - 1 else d) else (if v = root then 0 else 1))
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    g.extensionGreen q z root root = cavityIterate z q (r + 1) := by
  have hmatrix : g.extensionMatrix q z = radialCavityMatrix g.graph d root r q z := by
    rw [g.extensionMatrix_one_root_deficit root hdeficit q z]
    unfold forestReferenceMatrix radialCavityMatrix
    have hD : (Matrix.diagonal (fun v => (forestBoundaryCoefficient g.graph d root 1 v : ℂ))) =
        Matrix.diagonal (fun v => if g.graph.dist v root = r then 1 else 0) := by
      apply congrArg (fun f : V → ℂ => Matrix.diagonal f)
      funext v
      rw [homogeneous_forest_boundary_coefficient g.graph d hd root r hheight hdegree v]
      split_ifs <;> rfl
    rw [hD]
  change (g.extensionMatrix q z)⁻¹ root root = _
  rw [hmatrix]
  exact radialCavityMatrix_inverse_root g.graph d hd root r hG hheight hdegree q z hz hq

end DeficientGraph
end LocalLaw
