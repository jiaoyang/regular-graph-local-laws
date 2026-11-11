import LocalLaw.BoundedExcessStability
import LocalLaw.TreeBoundaryMass
import LocalLaw.SpectralGap

/-!
# Refined boundary feedback on an actual finite cavity tree

The first derivative at the physical boundary is close to one because the
critical cavity boundary mass is exactly one. The second-order correction
is controlled by the proved weighted kernel convolution.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance cavityFeedbackDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem unit_disk_power_sub_one (a : ℂ) (ha : ‖a‖ ≤ 1) (n : ℕ) :
    ‖a ^ n - 1‖ ≤ (n : ℝ) * ‖a - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : a ^ (n + 1) - 1 = a * (a ^ n - 1) + (a - 1) := by rw [pow_succ]; ring
    rw [heq]
    calc
      _ ≤ ‖a * (a ^ n - 1)‖ + ‖a - 1‖ := norm_add_le _ _
      _ = ‖a‖ * ‖a ^ n - 1‖ + ‖a - 1‖ := by rw [norm_mul]
      _ ≤ 1 * ((n : ℝ) * ‖a - 1‖) + ‖a - 1‖ :=
        add_le_add_right (mul_le_mul ha ih (norm_nonneg _) (by norm_num)) _
      _ = _ := by push_cast; ring

section WeightedDerivative
variable {V : Type*} [Fintype V]

theorem weighted_power_derivative_bound (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hmass : ∑ v, w v = 1) (depth : V → ℕ) (R : ℕ) (hdepth : ∀ v, depth v ≤ R)
    (m : ℂ) (hm : ‖m‖ ≤ 1) :
    ‖(∑ v, (w v : ℂ) * (m ^ 2) ^ (depth v + 1)) - 1‖ ≤
      ((R : ℝ) + 1) * ‖m ^ 2 - 1‖ := by
  have hmassC : ∑ v, (w v : ℂ) = 1 := by exact_mod_cast hmass
  have heq : (∑ v, (w v : ℂ) * (m ^ 2) ^ (depth v + 1)) - 1 =
      ∑ v, (w v : ℂ) * ((m ^ 2) ^ (depth v + 1) - 1) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hmassC]
  have hm2 : ‖m ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hm
  rw [heq]
  calc
    _ ≤ ∑ v, ‖(w v : ℂ) * ((m ^ 2) ^ (depth v + 1) - 1)‖ := norm_sum_le _ _
    _ ≤ ∑ v, w v * (((R : ℝ) + 1) * ‖m ^ 2 - 1‖) := by
      apply Finset.sum_le_sum
      intro v _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw v)]
      apply mul_le_mul_of_nonneg_left _ (hw v)
      apply (unit_disk_power_sub_one (m ^ 2) hm2 (depth v + 1)).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact_mod_cast Nat.add_le_add_right (hdepth v) 1
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

end WeightedDerivative

section FiniteTree
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

def cavityTreeDerivative (d : ℕ) (root : V) (m : ℂ) : ℂ :=
  ∑ v, (forestBoundaryCoefficient G d root 1 v : ℂ) * m ^ 2 *
    (-m * treeEdgeWeight d) ^ (2 * G.dist v root)

theorem cavityTreeDerivative_eq_mass (d : ℕ) (hd : 3 ≤ d) (root : V) (m : ℂ) :
    cavityTreeDerivative G d root m = ∑ v,
      ((forestBoundaryCoefficient G d root 1 v * treeFlowWeight G root ((d : ℝ) - 1) v : ℝ) : ℂ) *
        (m ^ 2) ^ (G.dist v root + 1) := by
  apply Finset.sum_congr rfl
  intro v _
  have ht : (-m * treeEdgeWeight d) ^ 2 = m ^ 2 * (((d : ℝ) - 1)⁻¹ : ℝ) := by
    rw [mul_pow, neg_sq, treeEdgeWeight_sq d hd]
    simp only [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one]
    ring
  rw [pow_mul, ht, mul_pow]
  simp only [treeFlowWeight, Complex.ofReal_mul, Complex.ofReal_pow, pow_succ]
  ring

theorem cavityTreeDerivative_bound (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d) (root : V)
    (hdeg : ∀ v, G.degree v + (if v = root then 1 else 0) ≤ d)
    (m : ℂ) (hm : ‖m‖ ≤ 1) (R : ℕ) (hR : ∀ v, G.dist v root ≤ R) :
    ‖cavityTreeDerivative G d root m - 1‖ ≤ ((R : ℝ) + 1) * ‖m ^ 2 - 1‖ := by
  rw [cavityTreeDerivative_eq_mass G d hd root m]
  apply weighted_power_derivative_bound
    (fun v => forestBoundaryCoefficient G d root 1 v * treeFlowWeight G root ((d : ℝ) - 1) v)
    _ (tree_cavity_boundary_mass G hG d hd root) _ R hR m hm
  intro v
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  exact mul_nonneg (forestBoundaryCoefficient_nonnegative G d hd root 1 hdeg v)
    (treeFlowWeight_nonneg G root _ (by linarith) v)

theorem forestReferenceMatrix_transpose (d : ℕ) (root : V) (b : ℕ) (m z : ℂ) :
    (forestReferenceMatrix G d root b m z).transpose = forestReferenceMatrix G d root b m z := by
  have hH : (normalizedAdjacency G d).transpose = normalizedAdjacency G d := by
    ext i j
    simp only [normalizedAdjacency, Matrix.transpose_apply, Matrix.smul_apply,
      smul_eq_mul, SimpleGraph.adjMatrix_apply]
    rw [G.adj_comm]
  simp only [forestReferenceMatrix, boundaryMatrix, spectralMatrix, Matrix.transpose_sub,
    Matrix.transpose_smul, Matrix.transpose_one, Matrix.diagonal_transpose, hH]

theorem forestReference_inverse_symmetric (d : ℕ) (root : V) (b : ℕ) (m z : ℂ) (i j : V) :
    (forestReferenceMatrix G d root b m z)⁻¹ i j =
      (forestReferenceMatrix G d root b m z)⁻¹ j i := by
  have hh := congrArg (fun M : Matrix V V ℂ => M j i)
    (show ((forestReferenceMatrix G d root b m z)⁻¹).transpose =
      (forestReferenceMatrix G d root b m z)⁻¹ by
      rw [Matrix.transpose_nonsing_inv, forestReferenceMatrix_transpose])
  exact hh

/-- The exact derivative of the cavity-root inverse with respect to its
boundary value is the boundary-mass polynomial. -/
theorem cavityTreeDerivative_eq_inverse_product (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (root : V) (hdeg : ∀ v, G.degree v + (if v = root then 1 else 0) ≤ d)
    (m z : ℂ) (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hmim : 0 ≤ m.im) :
    ((forestReferenceMatrix G d root 1 m z)⁻¹ *
      Matrix.diagonal (fun v => (forestBoundaryCoefficient G d root 1 v : ℂ)) *
      (forestReferenceMatrix G d root 1 m z)⁻¹) root root = cavityTreeDerivative G d root m := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro v _
  rw [forestReference_inverse_symmetric G d root 1 m z root v,
    forestReference_cavity_column G hG.IsAcyclic d hd root hdeg m z hm hz hmim v]
  simp only [forestKernelColumn, if_pos (hG.isConnected.preconnected v root)]
  have heq : 2 * G.dist v root = G.dist v root + G.dist v root := by omega
  rw [heq, pow_add]
  ring

/-- Refined source Proposition 2.11 for every actual finite rooted tree.
Critical boundary mass removes the linear error at an edge, leaving the
physical root gap times the boundary error and a quadratic remainder. -/
theorem cavity_tree_refined_feedback (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d) (root : V)
    (hdeg : ∀ v, G.degree v + (if v = root then 1 else 0) ≤ d)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j, G.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * 3 * (3 / 2 : ℝ) * ((R : ℝ) + 1) ≤ 1 / 2) :
    ‖(forestReferenceMatrix G d root 1 q z)⁻¹ root root - q‖ ≤
      ((R : ℝ) + 1) * (‖(semicircleRoot z) ^ 2 - 1‖ * ‖q - semicircleRoot z‖ +
        128 * ‖q - semicircleRoot z‖ ^ 2) := by
  let m := semicircleRoot z
  let t := physicalTransfer d z
  let δ := ‖q - m‖
  let Dw := forestBoundaryCoefficient G d root 1
  let D := Matrix.diagonal (fun v => (Dw v : ℂ))
  let H := normalizedAdjacency G d
  let Pm := (forestReferenceMatrix G d root 1 m z)⁻¹
  let Pq := (forestReferenceMatrix G d root 1 q z)⁻¹
  let K : V → V → ℝ := fun i j => t ^ G.dist i j
  let B : V → V → ℝ := fun i j => ((G.dist i j : ℝ) + 1) * K i j
  have htpos : 0 < t := physicalTransfer_pos d hd z
  have hD : ∀ v, 0 ≤ Dw v := forestBoundaryCoefficient_nonnegative G d hd root 1 hdeg
  have hK : ∀ i j, 0 ≤ K i j := fun i j => pow_nonneg htpos.le _
  have hB : ∀ i j, 0 < B i j := fun i j => mul_pos (by positivity) (pow_pos htpos _)
  have hδ : 0 ≤ δ := norm_nonneg _
  have hRpos : 0 < (R : ℝ) + 1 := by positivity
  have htmax : t ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹ := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hα : 0 ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹ := by positivity
    change ‖-m * treeEdgeWeight d‖ ≤ _
    rw [norm_mul, norm_neg]
    have he : ‖treeEdgeWeight d‖ = (Real.sqrt ((d : ℝ) - 1))⁻¹ := by
      simp only [treeEdgeWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hα]
    rw [he]
    exact (mul_le_mul_of_nonneg_right (semicircleRoot_norm_le_one z) hα).trans_eq (one_mul _)
  have hconv : ∀ i j, (∑ v, Dw v * K i v * K v j) ≤ (3 / 2 : ℝ) * B i j := by
    intro i j
    simpa only [Dw, K, B, add_comm, mul_assoc] using
      tree_root_deficit_convolution G hG d hd root 1 hdeg t htpos.le htmax i j
  have hcomp : ∀ i j, B i j ≤ ((R : ℝ) + 1) * K i j := by
    intro i j
    exact mul_le_mul_of_nonneg_right (add_le_add_right (Nat.cast_le.mpr (hR i j)) 1) (hK i j)
  have href : ∀ i j, ‖Pm i j‖ ≤ 3 * K i j :=
    root_deficit_tree_entry_bound G hG d hd root hdeg z hz
  have hunitq : IsUnit (boundaryMatrix H D q z) := forestReferenceMatrix_isUnit G d hd root 1 hdeg q z hz hq
  have hunitm : IsUnit (boundaryMatrix H D m z) := forestReferenceMatrix_isUnit G d hd root 1 hdeg m z hz (semicircleRoot_im_pos hz).le
  have hpert := boundary_kernel_stability H Dw q m z hunitq hunitm K B 3 (3 / 2) ((R : ℝ) + 1)
    hD hK hB (by norm_num) (by norm_num) hRpos.le href hcomp hconv small
  have hdiff : ∀ i j, ‖(Pq - Pm) i j‖ ≤ (27 * δ * ((R : ℝ) + 1)) * K i j := by
    intro i j
    have hh := (hpert i j).1
    change ‖(Pq - Pm) i j‖ ≤ 2 * δ * 3 ^ 2 * (3 / 2 : ℝ) * B i j at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (hcomp i j) (by positivity)).trans_eq (by ring))
  have hconvroot : (∑ v, Dw v * K root v * K v root) ≤ (3 / 2 : ℝ) := by
    simpa only [B, K, G.dist_self, pow_zero, Nat.cast_zero, zero_add, mul_one] using hconv root root
  have hrem0 := diagonal_kernel_product_bound Pm (Pq - Pm) Dw K K 3 (27 * δ * ((R : ℝ) + 1))
    hD hK (by norm_num) (by positivity) href hdiff root root (3 / 2) hconvroot
  have hrem : ‖(Pm * D * (Pq - Pm)) root root‖ ≤ 128 * δ * ((R : ℝ) + 1) := by
    apply hrem0.trans
    nlinarith
  have hF := cavityTreeDerivative_bound G hG d hd root hdeg m (semicircleRoot_norm_le_one z) R (fun v => hR v root)
  have hid := congrArg (fun M : Matrix V V ℂ => M root root)
    (boundary_reference_resolvent_identity H D q m z hunitq hunitm)
  change Pq root root - Pm root root = (q - m) * (Pm * D * Pq) root root at hid
  have hsplit : Pm * D * Pq = Pm * D * Pm + Pm * D * (Pq - Pm) := by noncomm_ring
  rw [hsplit, Matrix.add_apply] at hid
  have hdiag : Pm root root = m := forestReference_cavity_diagonal G hG.IsAcyclic d hd root hdeg m z
    (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le
  have hprod : (Pm * D * Pm) root root = cavityTreeDerivative G d root m :=
    cavityTreeDerivative_eq_inverse_product G hG d hd root hdeg m z (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le
  rw [hdiag, hprod] at hid
  have heq : Pq root root - q = (q - m) * (cavityTreeDerivative G d root m - 1) +
      (q - m) * (Pm * D * (Pq - Pm)) root root := by linear_combination hid
  rw [heq]
  calc
    _ ≤ ‖q - m‖ * ‖cavityTreeDerivative G d root m - 1‖ +
        ‖q - m‖ * ‖(Pm * D * (Pq - Pm)) root root‖ := by
      simpa only [norm_mul] using norm_add_le ((q - m) * (cavityTreeDerivative G d root m - 1))
        ((q - m) * (Pm * D * (Pq - Pm)) root root)
    _ ≤ δ * (((R : ℝ) + 1) * ‖m ^ 2 - 1‖) + δ * (128 * δ * ((R : ℝ) + 1)) :=
      add_le_add (mul_le_mul_of_nonneg_left hF hδ) (mul_le_mul_of_nonneg_left hrem hδ)
    _ = _ := by dsimp [δ, m]; ring

omit [Fintype V] [DecidableEq V] in
theorem physical_root_square_gap_bound (z : ℂ) (hz : 0 < z.im)
    (B : ℝ) (hB : ‖z‖ ≤ B) :
    ‖(semicircleRoot z) ^ 2 - 1‖ ≤ Real.sqrt (B + 2) * Real.sqrt (spectralScale z) := by
  let m := semicircleRoot z
  have hm0 : m ≠ 0 := semicircleRoot_ne_zero z
  have heq : m ^ 2 - 1 = -m * (m⁻¹ - m) := by rw [mul_sub, neg_mul, mul_inv_cancel₀ hm0]; ring
  rw [heq, norm_mul, norm_neg]
  apply (mul_le_mul_of_nonneg_right (semicircleRoot_norm_le_one z) (norm_nonneg _)).trans
  simpa only [one_mul] using (cavity_root_gap_bounds (semicircleRoot_equation z) hz hB).2

/-- Physical spectral-scale version of the actual finite-tree feedback. -/
theorem cavity_tree_spectral_feedback (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d) (root : V)
    (hdeg : ∀ v, G.degree v + (if v = root then 1 else 0) ≤ d)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (B : ℝ) (hB : ‖z‖ ≤ B)
    (R : ℕ) (hR : ∀ i j, G.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * 3 * (3 / 2 : ℝ) * ((R : ℝ) + 1) ≤ 1 / 2) :
    ‖(forestReferenceMatrix G d root 1 q z)⁻¹ root root - q‖ ≤
      ((R : ℝ) + 1) * (Real.sqrt (B + 2) * Real.sqrt (spectralScale z) *
        ‖q - semicircleRoot z‖ + 128 * ‖q - semicircleRoot z‖ ^ 2) := by
  apply (cavity_tree_refined_feedback G hG d hd root hdeg z q hz hq R hR small).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add_right (mul_le_mul_of_nonneg_right (physical_root_square_gap_bound z hz B hB)
    (norm_nonneg _)) _

end FiniteTree

namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

theorem extensionMatrix_one_root_deficit (g : DeficientGraph V d) (root : V)
    (hdeficit : ∀ v, g.deficit v = if v = root then 1 else 0) (q z : ℂ) :
    g.extensionMatrix q z = forestReferenceMatrix g.graph d root 1 q z := by
  have hcoeff : ∀ v, g.boundaryCoefficient v = forestBoundaryCoefficient g.graph d root 1 v := by
    intro v
    by_cases hv : v = root <;> simp [boundaryCoefficient, forestBoundaryCoefficient, hdeficit, hv]
  have hD : g.boundaryDiagonal = Matrix.diagonal
      (fun v => (forestBoundaryCoefficient g.graph d root 1 v : ℂ)) := by
    simp only [boundaryDiagonal, hcoeff]
  simp only [extensionMatrix, forestReferenceMatrix, H, hD]

/-- The refined feedback applies to the literal deficient models of deleted
tree components, using only their actual one-root deficit convention. -/
theorem one_root_tree_spectral_feedback (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.IsTree) (root : V)
    (hdeficit : ∀ v, g.deficit v = if v = root then 1 else 0)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (B : ℝ) (hB : ‖z‖ ≤ B)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * 3 * (3 / 2 : ℝ) * ((R : ℝ) + 1) ≤ 1 / 2) :
    ‖g.extensionGreen q z root root - q‖ ≤
      ((R : ℝ) + 1) * (Real.sqrt (B + 2) * Real.sqrt (spectralScale z) *
        ‖q - semicircleRoot z‖ + 128 * ‖q - semicircleRoot z‖ ^ 2) := by
  have hdeg : ∀ v, g.graph.degree v + (if v = root then 1 else 0) ≤ d := by
    intro v
    simpa only [hdeficit v] using g.degree_deficit_le v
  change ‖(g.extensionMatrix q z)⁻¹ root root - q‖ ≤ _
  rw [g.extensionMatrix_one_root_deficit root hdeficit q z]
  exact cavity_tree_spectral_feedback g.graph hG d hd root hdeg z q hz hq B hB R hR small

end DeficientGraph
end LocalLaw
