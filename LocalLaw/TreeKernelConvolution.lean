import LocalLaw.TreeBoundaryMass
import LocalLaw.KernelBoundaryStability

/-!
# Exact tree boundary-kernel convolution

A distance-weighted critical column is verified by the unique-parent rule.
The two finite matrix identities AK=sI and AJ+DK=qI give the exact boundary
convolution KDK=qK-sJ. No infinite tree, projection estimate, or convergence
statement is assumed.
-/

open scoped BigOperators Matrix
set_option maxHeartbeats 800000

namespace LocalLaw
noncomputable section
local instance treeConvolutionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section FiniteTree
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Full-tree boundary deficit, independent of a distinguished root. -/
def treeBoundaryWeight (d : ℕ) (v : V) : ℝ :=
  ((d : ℝ) - (G.degree v : ℝ)) / ((d : ℝ) - 1)

def treeBoundaryDiagonal (d : ℕ) : Matrix V V ℂ :=
  Matrix.diagonal (fun v => (treeBoundaryWeight G d v : ℂ))

/-- Positive critical tree kernel. -/
def treePowerKernel (t : ℂ) : Matrix V V ℂ := fun i j => t ^ G.dist i j

/-- Distance-weighted critical column, the formal radial derivative. -/
def treeDistanceColumn (root : V) (t : ℂ) (v : V) : ℂ :=
  (G.dist v root : ℂ) * t ^ G.dist v root

/-- Critical reference matrix at m=-1,z=2. -/
def treeCriticalMatrix (d : ℕ) : Matrix V V ℂ :=
  spectralMatrix (normalizedAdjacency G d) 2 + treeBoundaryDiagonal G d

theorem treeBoundaryWeight_eq_forest (d : ℕ) (root v : V) :
    treeBoundaryWeight G d v = forestBoundaryCoefficient G d root 0 v := by
  simp [treeBoundaryWeight, forestBoundaryCoefficient]

theorem treeCriticalMatrix_eq_reference (d : ℕ) (root : V) :
    treeCriticalMatrix G d = forestReferenceMatrix G d root 0 (-1) 2 := by
  simp only [treeCriticalMatrix, forestReferenceMatrix, boundaryMatrix,
    treeBoundaryDiagonal, treeBoundaryWeight_eq_forest G d root,
    neg_smul, one_smul, sub_neg_eq_add]

omit [DecidableEq V] in
/-- Root neighbor sum for the distance-weighted column. -/
theorem treeDistanceColumn_root_neighbor_sum (root : V) (t : ℂ) :
    (∑ w ∈ G.neighborFinset root, treeDistanceColumn G root t w) = (G.degree root : ℂ) * t := by
  calc
    _ = ∑ _w ∈ G.neighborFinset root, t := by
      apply Finset.sum_congr rfl
      intro w hw
      have hadj := (G.mem_neighborFinset root w).mp hw
      simp only [treeDistanceColumn, SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm,
        Nat.cast_one, pow_one, one_mul]
    _ = _ := by simp [nsmul_eq_mul]

/-- Exact nonroot neighbor sum of the distance-weighted column. -/
theorem treeDistanceColumn_neighbor_sum (root v parent : V) (t : ℂ)
    (hvp : G.Adj v parent) (hp : G.dist parent root + 1 = G.dist v root)
    (hfar : ∀ w, G.Adj v w → w ≠ parent → G.dist w root = G.dist v root + 1) :
    (∑ w ∈ G.neighborFinset v, treeDistanceColumn G root t w) =
      ((G.degree v : ℂ) - 1) * (G.dist parent root + 2 : ℕ) * t ^ (G.dist parent root + 2) +
        (G.dist parent root : ℂ) * t ^ G.dist parent root := by
  have hmem : parent ∈ G.neighborFinset v := (G.mem_neighborFinset v parent).mpr hvp
  have hcardNat := Finset.card_erase_add_one hmem
  have hcard : (((G.neighborFinset v).erase parent).card : ℂ) = (G.degree v : ℂ) - 1 := by
    have hh : (((G.neighborFinset v).erase parent).card : ℂ) + 1 = G.degree v := by exact_mod_cast hcardNat
    linear_combination hh
  rw [← Finset.sum_erase_add (G.neighborFinset v) (treeDistanceColumn G root t) hmem]
  have hsum : (∑ w ∈ (G.neighborFinset v).erase parent, treeDistanceColumn G root t w) =
      (((G.neighborFinset v).erase parent).card : ℂ) *
        ((G.dist parent root + 2 : ℕ) * t ^ (G.dist parent root + 2)) := by
    calc
      _ = ∑ _w ∈ (G.neighborFinset v).erase parent,
          (G.dist parent root + 2 : ℕ) * t ^ (G.dist parent root + 2) := by
        apply Finset.sum_congr rfl
        intro w hw
        have hadj := (G.mem_neighborFinset v w).mp (Finset.mem_of_mem_erase hw)
        have hd := hfar w hadj (Finset.mem_erase.mp hw).1
        have hd' : G.dist w root = G.dist parent root + 2 := by omega
        simp only [treeDistanceColumn, hd']
      _ = _ := by simp [nsmul_eq_mul]
  rw [hsum, hcard, treeDistanceColumn]
  ring

/-- The critical matrix acts on the positive power column by the scalar
s=d/(d-1)-2 at its root. -/
theorem treeCriticalMatrix_power_column (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d) (root : V) :
    treeCriticalMatrix G d *ᵥ (fun v => treeEdgeWeight d ^ G.dist v root) =
      Pi.single root ((d : ℂ) / ((d : ℂ) - 1) - 2) := by
  rw [treeCriticalMatrix_eq_reference G d root]
  have hm : (-1 : ℂ) ^ 2 + 2 * (-1) + 1 = 0 := by norm_num
  have hh := forestReferenceMatrix_column G hG.IsAcyclic d hd root 0 (-1) 2 1 hm
  have hr : ∀ v, G.Reachable v root := fun v => hG.isConnected.preconnected v root
  have hcol : forestKernelColumn G root 1 (treeEdgeWeight d) =
      fun v => treeEdgeWeight d ^ G.dist v root := by
    funext v
    simp only [forestKernelColumn, if_pos (hr v), one_mul]
  simp only [neg_neg, one_mul, Nat.cast_zero, sub_zero, mul_neg, mul_one] at hh
  rw [hcol] at hh
  convert hh using 1
  ring_nf

/-- Direct finite verification of the formal radial derivative column.
The derivative of z(m)=-m-m^-1 vanishes at the critical value m=-1. -/
theorem treeCriticalMatrix_distance_column (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d) (root : V) :
    treeCriticalMatrix G d *ᵥ treeDistanceColumn G root (treeEdgeWeight d) +
      treeBoundaryDiagonal G d *ᵥ (fun v => treeEdgeWeight d ^ G.dist v root) =
        Pi.single root ((d : ℂ) / ((d : ℂ) - 1)) := by
  have hk : (d : ℂ) - 1 ≠ 0 := by
    have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
    intro heq
    have hh := congrArg Complex.re heq
    simp at hh
    linarith
  funext v
  rw [Pi.add_apply, treeCriticalMatrix_eq_reference G d root,
    forestReferenceMatrix_mulVec, treeBoundaryDiagonal, Matrix.mulVec_diagonal]
  simp only [Pi.mul_apply, treeBoundaryWeight_eq_forest G d root, forestBoundaryCoefficient_complex,
    Nat.cast_zero, ite_self, sub_zero, neg_mul, one_mul, sub_neg_eq_add]
  by_cases hv : v = root
  · subst v
    rw [treeDistanceColumn_root_neighbor_sum]
    simp only [treeDistanceColumn, G.dist_self, Nat.cast_zero, pow_zero, zero_mul,
      mul_zero, sub_zero, mul_one, Pi.single_apply, if_pos rfl]
    simp only [ite_true]
    linear_combination (G.degree root : ℂ) * treeEdgeWeight_sq d hd
  · obtain ⟨parent, hvp, hp, hfar⟩ := forest_parent_distance hG.IsAcyclic root v
      (hG.isConnected.preconnected v root) hv
    rw [treeDistanceColumn_neighbor_sum G root v parent _ hvp hp hfar]
    simp only [treeDistanceColumn, ← hp, Pi.single_apply, if_neg hv,
      Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    simp only [pow_add, pow_one]
    rw [treeEdgeWeight_sq d hd]
    field_simp
    ring

/-- Exact critical boundary convolution, derived entirely from finite
matrix products and the verified tree columns. -/
theorem tree_critical_convolution (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d) (i j : V) :
    (∑ x, (treeBoundaryWeight G d x : ℂ) *
      treeEdgeWeight d ^ G.dist i x * treeEdgeWeight d ^ G.dist x j) =
        (((d : ℂ) / ((d : ℂ) - 1)) +
          (((d : ℂ) - 2) / ((d : ℂ) - 1)) * G.dist i j) * treeEdgeWeight d ^ G.dist i j := by
  let A := treeCriticalMatrix G d
  let K := treePowerKernel G (treeEdgeWeight d)
  let J : Matrix V V ℂ := fun i j => treeDistanceColumn G j (treeEdgeWeight d) i
  let D := treeBoundaryDiagonal G d
  let q := (d : ℂ) / ((d : ℂ) - 1)
  have hAK : A * K = q • 1 - (2 : ℂ) • 1 := by
    ext a b
    have hh := congrFun (treeCriticalMatrix_power_column G hG d hd b) a
    by_cases hab : a = b <;> simpa [A, K, q, treePowerKernel, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Pi.single_apply, hab] using hh
  have hAsymm : A.transpose = A := by
    simp only [A, treeCriticalMatrix, spectralMatrix, treeBoundaryDiagonal,
      Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one, Matrix.diagonal_transpose, normalizedAdjacency]
    rw [G.isSymm_adjMatrix.eq]
  have hKsymm : K.transpose = K := by
    ext a b
    exact congrArg (fun n => treeEdgeWeight d ^ n) (show G.dist b a = G.dist a b from G.dist_comm)
  have hKA : K * A = q • 1 - (2 : ℂ) • 1 := by
    have hh := congrArg Matrix.transpose hAK
    simpa only [Matrix.transpose_mul, hAsymm, hKsymm, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one] using hh
  have hAJ : A * J + D * K = q • 1 := by
    ext a b
    have hh := congrFun (treeCriticalMatrix_distance_column G hG d hd b) a
    by_cases hab : a = b <;> simpa [A, J, D, K, q, treePowerKernel, Matrix.add_apply, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Pi.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, Pi.single_apply, hab] using hh
  have hconv : K * D * K = q • K - (q - 2) • J := by
    have hh := congrArg (fun B : Matrix V V ℂ => K * B) hAJ
    dsimp only at hh
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hKA, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, ← Matrix.mul_assoc] at hh
    rw [← sub_smul] at hh
    apply (eq_sub_iff_add_eq).mpr
    simpa only [add_comm] using hh
  have hh := congrArg (fun M : Matrix V V ℂ => M i j) hconv
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
    K, J, treePowerKernel, treeDistanceColumn, D, treeBoundaryDiagonal,
    Matrix.diagonal_apply] at hh
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hh
  change _ = _
  calc
    _ = q * treeEdgeWeight d ^ G.dist i j -
        (q - 2) * ((G.dist i j : ℂ) * treeEdgeWeight d ^ G.dist i j) := by
      convert hh using 1
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      dsimp [q]
      have hk : (d : ℂ) - 1 ≠ 0 := by
        have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
        intro heq
        have hre := congrArg Complex.re heq
        simp at hre
        linarith
      field_simp
      ring

/-- Real form of the exact critical convolution. -/
theorem tree_critical_convolution_real (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d) (i j : V) :
    (∑ x, treeBoundaryWeight G d x *
      (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ G.dist i x * (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ G.dist x j) =
        (((d : ℝ) / ((d : ℝ) - 1)) +
          (((d : ℝ) - 2) / ((d : ℝ) - 1)) * G.dist i j) *
            (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ G.dist i j := by
  have hh := tree_critical_convolution G hG d hd i j
  unfold treeEdgeWeight at hh
  exact_mod_cast hh

/-- All subcritical radial rates satisfy the exact critical coefficient bound.
The factor t/alpha avoids any division by t, including at t=0. -/
theorem tree_boundary_convolution_sharp (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ v, G.degree v ≤ d) (t : ℝ) (ht : 0 ≤ t)
    (htmax : t ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹) (i j : V) :
    (∑ x, treeBoundaryWeight G d x * t ^ G.dist i x * t ^ G.dist x j) ≤
      (((d : ℝ) / ((d : ℝ) - 1)) +
        (((d : ℝ) - 2) / ((d : ℝ) - 1)) * G.dist i j) * t ^ G.dist i j := by
  let α := (Real.sqrt ((d : ℝ) - 1))⁻¹
  let u := t / α
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hkpos : 0 < (d : ℝ) - 1 := by linarith
  have hα : 0 < α := inv_pos.mpr (Real.sqrt_pos.mpr hkpos)
  have hu : 0 ≤ u := div_nonneg ht hα.le
  have huone : u ≤ 1 := (div_le_one hα).mpr htmax
  have htdecomp : t = u * α := (div_mul_cancel₀ t (ne_of_gt hα)).symm
  have hD : ∀ x, 0 ≤ treeBoundaryWeight G d x := by
    intro x
    exact div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr (hdeg x))) hkpos.le
  calc
    _ ≤ u ^ G.dist i j * (∑ x, treeBoundaryWeight G d x * α ^ G.dist i x * α ^ G.dist x j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x _
      have hp := pow_le_pow_of_le_one hu huone (hG.isConnected.dist_triangle (u := i) (v := x) (w := j))
      calc
        _ = u ^ (G.dist i x + G.dist x j) *
            (treeBoundaryWeight G d x * α ^ G.dist i x * α ^ G.dist x j) := by
          rw [htdecomp, mul_pow, mul_pow, pow_add]
          ring
        _ ≤ u ^ G.dist i j * (treeBoundaryWeight G d x * α ^ G.dist i x * α ^ G.dist x j) :=
          mul_le_mul_of_nonneg_right hp
            (mul_nonneg (mul_nonneg (hD x) (pow_nonneg hα.le _)) (pow_nonneg hα.le _))
    _ = u ^ G.dist i j *
        ((((d : ℝ) / ((d : ℝ) - 1)) + (((d : ℝ) - 2) / ((d : ℝ) - 1)) * G.dist i j) * α ^ G.dist i j) := by
      rw [tree_critical_convolution_real G hG d hd i j]
    _ = _ := by rw [htdecomp, mul_pow]; ring

/-- Uniform finite-tree boundary convolution, with constant three halves. -/
theorem tree_boundary_convolution (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ v, G.degree v ≤ d) (t : ℝ) (ht : 0 ≤ t)
    (htmax : t ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹) (i j : V) :
    (∑ x, treeBoundaryWeight G d x * t ^ G.dist i x * t ^ G.dist x j) ≤
      (3 / 2 : ℝ) * (1 + G.dist i j) * t ^ G.dist i j := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hkpos : 0 < (d : ℝ) - 1 := by linarith
  have hq : (d : ℝ) / ((d : ℝ) - 1) ≤ 3 / 2 := (div_le_iff₀ hkpos).mpr (by linarith)
  have hs : ((d : ℝ) - 2) / ((d : ℝ) - 1) ≤ 3 / 2 :=
    (div_le_div_of_nonneg_right (by linarith : (d : ℝ) - 2 ≤ d) hkpos.le).trans hq
  exact (tree_boundary_convolution_sharp G hG d hd hdeg t ht htmax i j).trans
    (mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg (G.dist i j))]) (pow_nonneg ht _))

/-- Removing one or more root boundary deficits only decreases the convolution. -/
theorem tree_root_deficit_convolution (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (root : V) (b : ℕ) (hdeg : ∀ v, G.degree v + (if v = root then b else 0) ≤ d)
    (t : ℝ) (ht : 0 ≤ t) (htmax : t ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹) (i j : V) :
    (∑ x, forestBoundaryCoefficient G d root b x * t ^ G.dist i x * t ^ G.dist x j) ≤
      (3 / 2 : ℝ) * (1 + G.dist i j) * t ^ G.dist i j := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hkpos : 0 < (d : ℝ) - 1 := by linarith
  have hdeg' : ∀ v, G.degree v ≤ d := by intro v; have hh := hdeg v; omega
  apply le_trans _ (tree_boundary_convolution G hG d hd hdeg' t ht htmax i j)
  apply Finset.sum_le_sum
  intro x _
  have hD : forestBoundaryCoefficient G d root b x ≤ treeBoundaryWeight G d x := by
    dsimp only [forestBoundaryCoefficient, treeBoundaryWeight]
    apply div_le_div_of_nonneg_right _ hkpos.le
    have hb0 : (0 : ℝ) ≤ if x = root then (b : ℝ) else 0 := by split <;> positivity
    linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD (pow_nonneg ht _)) (pow_nonneg ht _)

/-- Full-tree reference matrices are independent of the irrelevant root label. -/
theorem forestReference_full_root_independent (d : ℕ) (root other : V) (m z : ℂ) :
    forestReferenceMatrix G d root 0 m z = forestReferenceMatrix G d other 0 m z := by
  simp [forestReferenceMatrix, forestBoundaryCoefficient]

/-- Exact norm of every entry of the genuine full-tree physical reference. -/
theorem forestReference_full_norm_kernel (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ v, G.degree v ≤ d) (root : V) (z : ℂ) (hz : 0 < z.im) (i j : V) :
    ‖(forestReferenceMatrix G d root 0 (semicircleRoot z) z)⁻¹ i j‖ =
      ‖kestenMcKayTransform d (semicircleRoot z) z‖ *
        (‖semicircleRoot z‖ / Real.sqrt ((d : ℝ) - 1)) ^ G.dist i j := by
  rw [forestReference_full_root_independent G d root j,
    forestReference_full_column G hG.IsAcyclic d hd j hdeg (semicircleRoot z) z
      (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le i]
  have hr := hG.isConnected.preconnected i j
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hs : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  have hbase : ‖-semicircleRoot z * treeEdgeWeight d‖ =
      ‖semicircleRoot z‖ / Real.sqrt ((d : ℝ) - 1) := by
    simp only [norm_mul, norm_neg, treeEdgeWeight, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), div_eq_mul_inv]
  rw [forestKernelColumn, if_pos hr, norm_mul, norm_pow, hbase]

/-- Boundary convolution for the actual finite full-tree reference inverse. -/
theorem forestReference_full_boundary_convolution (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ v, G.degree v ≤ d) (root : V) (z : ℂ) (hz : 0 < z.im) (i j : V) :
    (∑ x, treeBoundaryWeight G d x *
      ‖(forestReferenceMatrix G d root 0 (semicircleRoot z) z)⁻¹ i x‖ *
      ‖(forestReferenceMatrix G d root 0 (semicircleRoot z) z)⁻¹ x j‖) ≤
        6 * (1 + G.dist i j) *
          (‖semicircleRoot z‖ / Real.sqrt ((d : ℝ) - 1)) ^ G.dist i j := by
  let t := ‖semicircleRoot z‖ / Real.sqrt ((d : ℝ) - 1)
  let c := ‖kestenMcKayTransform d (semicircleRoot z) z‖
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hs : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  have ht : 0 ≤ t := div_nonneg (norm_nonneg _) hs.le
  have htmax : t ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹ := by
    rw [← one_div]
    exact div_le_div_of_nonneg_right (semicircleRoot_norm_le_one z) hs.le
  have hc : c ^ 2 ≤ 4 := by
    have hh := kestenMcKayTransform_norm_le_two d hd z hz
    have hc0 : 0 ≤ c := norm_nonneg _
    dsimp [c]
    nlinarith
  simp_rw [forestReference_full_norm_kernel G hG d hd hdeg root z hz]
  calc
    _ = c ^ 2 * (∑ x, treeBoundaryWeight G d x * t ^ G.dist i x * t ^ G.dist x j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      dsimp [c, t]
      ring
    _ ≤ c ^ 2 * ((3 / 2 : ℝ) * (1 + G.dist i j) * t ^ G.dist i j) :=
      mul_le_mul_of_nonneg_left (tree_boundary_convolution G hG d hd hdeg t ht htmax i j) (sq_nonneg _)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hc
        (show 0 ≤ (3 / 2 : ℝ) * (1 + G.dist i j) * t ^ G.dist i j by positivity)
      convert hh using 1
      dsimp [t]
      ring

/-- The genuine full-tree finite boundary resolvent with its root-free deficit. -/
def fullTreeGreen (d : ℕ) (w z : ℂ) : Matrix V V ℂ :=
  boundaryGreen (normalizedAdjacency G d) (treeBoundaryDiagonal G d) w z

theorem fullTreeGreen_eq_reference (d : ℕ) (root : V) (w z : ℂ) :
    fullTreeGreen G d w z = (forestReferenceMatrix G d root 0 w z)⁻¹ := by
  simp only [fullTreeGreen, boundaryGreen, treeBoundaryDiagonal,
    treeBoundaryWeight_eq_forest G d root, forestReferenceMatrix]

omit [DecidableEq V] in
/-- Every tree distance is smaller than its actual finite vertex count. -/
theorem tree_distance_succ_le_card (hG : G.IsTree) (i j : V) :
    G.dist i j + 1 ≤ Fintype.card V := by
  obtain ⟨p, hp, hlen⟩ := (hG.isConnected.preconnected i j).exists_path_of_dist
  have hh := hp.length_lt
  omega

/-- Actual finite-tree version of the boundary-kernel stability estimate.
The kernel, convolution, nonsingularity and diameter estimates are proved;
only the explicit smallness of the perturbed boundary weight is required. -/
theorem fullTreeGreen_boundary_stability (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ v, G.degree v ≤ d) (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (small : 3 * (Fintype.card V : ℝ) * ‖q - semicircleRoot z‖ ≤ 1 / 2) (i j : V) :
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
  have hcompanion : ∀ a b, B a b ≤ (Fintype.card V : ℝ) * K a b := by
    intro a b
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg ht.le _)
    have hh : ((G.dist a b + 1 : ℕ) : ℝ) ≤ Fintype.card V := Nat.cast_le.mpr (tree_distance_succ_le_card G hG a b)
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using hh
  have hconvolution : ∀ a b, (∑ x, treeBoundaryWeight G d x * K a x * K x b) ≤ (3 / 2 : ℝ) * B a b := by
    intro a b
    have hh := tree_boundary_convolution G hG d hd hdeg t ht.le htmax a b
    convert hh using 1
    dsimp [B, K]
    ring
  have hsmall : ‖q - m‖ * 2 * (3 / 2 : ℝ) * (Fintype.card V : ℝ) ≤ 1 / 2 := by
    convert small using 1
    dsimp [m]
    ring
  have hh := boundary_kernel_stability (normalizedAdjacency G d) (treeBoundaryWeight G d)
    q m z hunitq hunitm K B 2 (3 / 2) (Fintype.card V : ℝ) hD
    (fun a b => pow_nonneg ht.le _) (fun a b => mul_pos (by positivity) (pow_pos ht _))
    (by norm_num) (by norm_num) (Nat.cast_nonneg _) hreference hcompanion hconvolution hsmall i j
  constructor
  · convert hh.1 using 1
    dsimp [B, K, t, m]
    ring
  · simpa only [K, t, m, show (2 : ℝ) * 2 = 4 by norm_num] using hh.2

/-- Actual two-weight tree boundary Lipschitz estimate. Its decay kernel and
all inverse/convolution requirements are consequences of the tree geometry. -/
theorem fullTreeGreen_two_weight_lipschitz (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ v, G.degree v ≤ d) (z q v : ℂ) (hz : 0 < z.im)
    (hq : 0 ≤ q.im) (hv : 0 ≤ v.im)
    (smallq : 3 * (Fintype.card V : ℝ) * ‖q - semicircleRoot z‖ ≤ 1 / 2)
    (smallv : 3 * (Fintype.card V : ℝ) * ‖v - semicircleRoot z‖ ≤ 1 / 2) (i j : V) :
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
    fun a b => (fullTreeGreen_boundary_stability G hG d hd hdeg z q hz hq smallq a b).2
  have hvbound : ∀ a b, ‖fullTreeGreen G d v z a b‖ ≤ 4 * K a b :=
    fun a b => (fullTreeGreen_boundary_stability G hG d hd hdeg z v hz hv smallv a b).2
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

end FiniteTree
end
end LocalLaw
