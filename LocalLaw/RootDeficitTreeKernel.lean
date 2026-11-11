import LocalLaw.UnicyclicImagBounds

/-!
# Exact one-root-deficit reference kernel on a finite tree

The genuine inverse difference is rank one. The already verified cavity-root
column evaluates one factor, so no Sherman--Morrison denominator is assumed.
-/

open scoped BigOperators Matrix
namespace LocalLaw
noncomputable section
local instance rootDeficitDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section FiniteTree
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Rank-one diagonal products evaluate at the actual distinguished vertex. -/
theorem root_diagonal_product (A B : Matrix V V ℂ) (root : V) (c : ℂ) (i j : V) :
    (A * Matrix.diagonal (fun x => if x = root then c else 0) * B) i j = A i root * c * B root j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The one-unit root deficit changes the actual finite operator by exactly
one diagonal entry. -/
theorem forestReference_root_deficit_difference (d : ℕ) (root : V) (m z : ℂ) :
    forestReferenceMatrix G d root 0 m z - forestReferenceMatrix G d root 1 m z =
      Matrix.diagonal (fun x => if x = root then -m / ((d : ℂ) - 1) else 0) := by
  ext i j
  simp only [forestReferenceMatrix, boundaryMatrix, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.diagonal_apply]
  rw [forestBoundaryCoefficient_complex G d root 0 i, forestBoundaryCoefficient_complex G d root 1 i]
  simp only [Nat.cast_zero, Nat.cast_one]
  split_ifs <;> ring

/-- Exact actual full zero-deficit kernel on a connected finite tree. -/
theorem forestReference_full_kernel (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ v, G.degree v ≤ d) (root : V) (m z : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hmim : 0 ≤ m.im) (i j : V) :
    (forestReferenceMatrix G d root 0 m z)⁻¹ i j =
      kestenMcKayTransform d m z * (-m * treeEdgeWeight d) ^ G.dist i j := by
  rw [forestReference_full_root_independent G d root j,
    forestReference_full_column G hG.IsAcyclic d hd j hdeg m z hm hz hmim i]
  simp only [forestKernelColumn, if_pos (hG.isConnected.preconnected i j)]

/-- The actual one-root-deficit inverse is the full tree kernel minus its
single reflected image term. -/
theorem forestReference_root_deficit_kernel (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (root : V) (hdeg : ∀ v, G.degree v + (if v = root then 1 else 0) ≤ d)
    (m z : ℂ) (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hmim : 0 ≤ m.im) (i j : V) :
    (forestReferenceMatrix G d root 1 m z)⁻¹ i j = kestenMcKayTransform d m z *
      ((-m * treeEdgeWeight d) ^ G.dist i j -
        (-m * treeEdgeWeight d) ^ (G.dist i root + G.dist root j + 2)) := by
  let A₀ := forestReferenceMatrix G d root 0 m z
  let A₁ := forestReferenceMatrix G d root 1 m z
  have hdeg₀ : ∀ v, G.degree v ≤ d := by intro v; have hh := hdeg v; omega
  have hdeg₀' : ∀ v, G.degree v + (if v = root then 0 else 0) ≤ d := by simpa only [ite_self, add_zero] using hdeg₀
  have hunit₀ : IsUnit A₀ := forestReferenceMatrix_isUnit G d hd root 0 hdeg₀' m z hz hmim
  have hunit₁ : IsUnit A₁ := forestReferenceMatrix_isUnit G d hd root 1 hdeg m z hz hmim
  have hid := Matrix.inv_sub_inv (show IsUnit A₁ ↔ IsUnit A₀ from ⟨fun _ => hunit₀, fun _ => hunit₁⟩)
  rw [forestReference_root_deficit_difference G d root m z] at hid
  have hh := congrArg (fun M : Matrix V V ℂ => M i j) hid
  dsimp only at hh
  rw [Matrix.sub_apply, root_diagonal_product,
    forestReference_cavity_column G hG.IsAcyclic d hd root hdeg m z hm hz hmim,
    forestReference_full_kernel G hG d hd hdeg₀ root m z hm hz hmim,
    forestReference_full_kernel G hG d hd hdeg₀ root m z hm hz hmim] at hh
  simp only [forestKernelColumn, if_pos (hG.isConnected.preconnected i root)] at hh
  have htsq : (-m * treeEdgeWeight d) ^ 2 = m ^ 2 / ((d : ℂ) - 1) := by
    rw [mul_pow, neg_sq, treeEdgeWeight_sq d hd]
    ring
  rw [pow_add, pow_add, htsq]
  linear_combination hh

/-- The one-deficit image term is smaller by at least one factor 1/2. -/
theorem root_deficit_tree_entry_bound (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (root : V) (hdeg : ∀ v, G.degree v + (if v = root then 1 else 0) ≤ d)
    (z : ℂ) (hz : 0 < z.im) (i j : V) :
    ‖(forestReferenceMatrix G d root 1 (semicircleRoot z) z)⁻¹ i j‖ ≤
      3 * ‖-semicircleRoot z * treeEdgeWeight d‖ ^ G.dist i j := by
  let m := semicircleRoot z
  let t := -m * treeEdgeWeight d
  let p := kestenMcKayTransform d m z
  have ht0 : 0 ≤ ‖t‖ := norm_nonneg _
  have ht1 : ‖t‖ ≤ 1 := (cycle_transfer_norm_le_three_quarters d hd m (semicircleRoot_norm_le_one z)).trans (by norm_num)
  have ht2 : ‖t‖ ^ 2 ≤ 1 / 2 := by
    have hsq : t ^ 2 = m ^ 2 / ((d : ℂ) - 1) := by
      dsimp [t]
      rw [mul_pow, neg_sq, treeEdgeWeight_sq d hd]
      ring
    rw [← norm_pow, hsq]
    exact physical_leaf_factor_norm d hd z
  have himage : ‖t‖ ^ (G.dist i root + G.dist root j + 2) ≤ (1 / 2 : ℝ) * ‖t‖ ^ G.dist i j := by
    rw [pow_add]
    have hp := pow_le_pow_of_le_one ht0 ht1 (hG.isConnected.dist_triangle (u := i) (v := root) (w := j))
    exact (mul_le_mul hp ht2 (sq_nonneg _) (pow_nonneg ht0 _)).trans_eq (mul_comm _ _)
  rw [forestReference_root_deficit_kernel G hG d hd root hdeg m z (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le, norm_mul]
  have hnum : ‖t ^ G.dist i j - t ^ (G.dist i root + G.dist root j + 2)‖ ≤
      (3 / 2 : ℝ) * ‖t‖ ^ G.dist i j := by
    exact (norm_sub_le _ _).trans (by rw [norm_pow, norm_pow]; linarith)
  have hp : ‖p‖ ≤ 2 := kestenMcKayTransform_norm_le_two d hd z hz
  exact (mul_le_mul hp hnum (norm_nonneg _) (by norm_num)).trans_eq (by ring)

/-- The actual root-deficit diagonal loses at most half of the full-tree
coefficient, independently of the tree shape and the root location. -/
theorem root_deficit_tree_diagonal_lower (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (root : V) (hdeg : ∀ v, G.degree v + (if v = root then 1 else 0) ≤ d)
    (z : ℂ) (hz : 0 < z.im) (i : V) :
    ‖kestenMcKayTransform d (semicircleRoot z) z‖ / 2 ≤
      ‖(forestReferenceMatrix G d root 1 (semicircleRoot z) z)⁻¹ i i‖ := by
  let t := -semicircleRoot z * treeEdgeWeight d
  have ht0 : 0 ≤ ‖t‖ := norm_nonneg _
  have ht1 : ‖t‖ ≤ 1 := (cycle_transfer_norm_le_three_quarters d hd _ (semicircleRoot_norm_le_one z)).trans (by norm_num)
  have ht2 : ‖t‖ ^ 2 ≤ 1 / 2 := by
    rw [← norm_pow, mul_pow, neg_sq, treeEdgeWeight_sq d hd]
    have hid : semicircleRoot z ^ 2 * (1 / ((d : ℂ) - 1)) = semicircleRoot z ^ 2 / ((d : ℂ) - 1) := by ring
    rw [hid]
    exact physical_leaf_factor_norm d hd z
  have hpow : ‖t ^ (G.dist i root + G.dist root i + 2)‖ ≤ 1 / 2 := by
    rw [norm_pow]
    exact (pow_le_pow_of_le_one ht0 ht1 (by omega : 2 ≤ G.dist i root + G.dist root i + 2)).trans ht2
  have hfactor : 1 / 2 ≤ ‖1 - t ^ (G.dist i root + G.dist root i + 2)‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) (t ^ (G.dist i root + G.dist root i + 2))
    rw [norm_one] at hh
    linarith
  rw [forestReference_root_deficit_kernel G hG d hd root hdeg _ z (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le,
    G.dist_self, pow_zero, norm_mul]
  exact (mul_le_mul_of_nonneg_left hfactor (norm_nonneg _)).trans_eq' (by ring)

end FiniteTree

/-- A single full-tree path kernel is a uniformly Lipschitz real-coefficient
function of the unit-disk free root. -/
def treeAnalyticKernel (d : ℕ) (a : ℂ) (k : ℕ) : ℂ :=
  rationalTreeReference (d - 1) a * (-a * treeEdgeWeight d) ^ k

theorem treeAnalyticKernel_lipschitz (d : ℕ) (hd : 3 ≤ d) (a b : ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (k : ℕ) :
    ‖treeAnalyticKernel d a k - treeAnalyticKernel d b k‖ ≤ 12 * ‖a - b‖ := by
  let ta := -a * treeEdgeWeight d
  let tb := -b * treeEdgeWeight d
  let pa := rationalTreeReference (d - 1) a
  let pb := rationalTreeReference (d - 1) b
  have hta := cycle_transfer_norm_le_three_quarters d hd a ha
  have htb := cycle_transfer_norm_le_three_quarters d hd b hb
  have hpower : ‖ta ^ k - tb ^ k‖ ≤ 3 * ‖a - b‖ :=
    (strict_disk_power_lipschitz ta tb hta htb k).trans (by nlinarith [cycle_transfer_lipschitz d hd a b])
  have hbound : ‖ta ^ k‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hta.trans (by norm_num))
  have hpLip : ‖pa - pb‖ ≤ 6 * ‖a - b‖ := rationalTreeReference_lipschitz (d - 1) (by omega) a b ha hb
  have hpB : ‖pb‖ ≤ 2 := rationalTreeReference_norm_le_two (d - 1) (by omega) b hb
  have hid : treeAnalyticKernel d a k - treeAnalyticKernel d b k =
      (pa - pb) * ta ^ k + pb * (ta ^ k - tb ^ k) := by dsimp [treeAnalyticKernel, pa, pb, ta, tb]; ring
  rw [hid]
  calc
    _ ≤ ‖(pa - pb) * ta ^ k‖ + ‖pb * (ta ^ k - tb ^ k)‖ := norm_add_le _ _
    _ ≤ (6 * ‖a - b‖) * 1 + 2 * (3 * ‖a - b‖) := by
      rw [norm_mul, norm_mul]
      exact add_le_add (mul_le_mul hpLip hbound (norm_nonneg _) (by positivity))
        (mul_le_mul hpB hpower (norm_nonneg _) (by norm_num))
    _ = _ := by ring

theorem treeAnalyticKernel_conj (d : ℕ) (a : ℂ) (k : ℕ) :
    treeAnalyticKernel d (starRingEnd ℂ a) k = starRingEnd ℂ (treeAnalyticKernel d a k) := by
  simp [treeAnalyticKernel, rationalTreeReference, treeEdgeWeight, map_div, map_sub, map_pow, map_mul]

/-- Reflection controls a full-tree path kernel by twelve times Imm. -/
theorem treeAnalyticKernel_im_bound (d : ℕ) (hd : 3 ≤ d) (a : ℂ)
    (ha : ‖a‖ ≤ 1) (him : 0 ≤ a.im) (k : ℕ) :
    |(treeAnalyticKernel d a k).im| ≤ 12 * a.im := by
  have hconj : ‖starRingEnd ℂ a‖ ≤ 1 := by simpa only [Complex.norm_conj] using ha
  have hh := treeAnalyticKernel_lipschitz d hd a (starRingEnd ℂ a) ha hconj k
  rw [treeAnalyticKernel_conj] at hh
  have hnorm : ∀ w : ℂ, ‖w - starRingEnd ℂ w‖ = 2 * |w.im| := by
    intro w
    rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    norm_num
  rw [hnorm, hnorm, abs_of_nonneg him] at hh
  linarith

section PhysicalTree
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- The actual full-tree reference has a uniform imaginary bound. -/
theorem forestReference_full_im_bound (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ v, G.degree v ≤ d) (root : V) (z : ℂ) (hz : 0 < z.im) (i j : V) :
    |((forestReferenceMatrix G d root 0 (semicircleRoot z) z)⁻¹ i j).im| ≤ 12 * (semicircleRoot z).im := by
  rw [forestReference_full_kernel G hG d hd hdeg root _ z (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le,
    kestenMcKayTransform_eq d hd _ z (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le]
  exact treeAnalyticKernel_im_bound d hd _ (semicircleRoot_norm_le_one z) (semicircleRoot_im_pos hz).le _

/-- The actual one-root-deficit reference inherits at most twice the path
imaginary bound from its exact reflected-image formula. -/
theorem root_deficit_tree_im_bound (hG : G.IsTree) (d : ℕ) (hd : 3 ≤ d)
    (root : V) (hdeg : ∀ v, G.degree v + (if v = root then 1 else 0) ≤ d)
    (z : ℂ) (hz : 0 < z.im) (i j : V) :
    |((forestReferenceMatrix G d root 1 (semicircleRoot z) z)⁻¹ i j).im| ≤ 24 * (semicircleRoot z).im := by
  rw [forestReference_root_deficit_kernel G hG d hd root hdeg _ z (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le,
    kestenMcKayTransform_eq d hd _ z (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le]
  have hid : rationalTreeReference (d - 1) (semicircleRoot z) *
      ((-semicircleRoot z * treeEdgeWeight d) ^ G.dist i j -
        (-semicircleRoot z * treeEdgeWeight d) ^ (G.dist i root + G.dist root j + 2)) =
      treeAnalyticKernel d (semicircleRoot z) (G.dist i j) -
        treeAnalyticKernel d (semicircleRoot z) (G.dist i root + G.dist root j + 2) := by
    dsimp [treeAnalyticKernel]
    ring
  dsimp only [rationalTreeReference] at hid
  rw [hid, Complex.sub_im]
  have h₁ := treeAnalyticKernel_im_bound d hd _ (semicircleRoot_norm_le_one z)
    (semicircleRoot_im_pos hz).le (G.dist i j)
  have h₂ := treeAnalyticKernel_im_bound d hd _ (semicircleRoot_norm_le_one z)
    (semicircleRoot_im_pos hz).le (G.dist i root + G.dist root j + 2)
  exact (abs_sub _ _).trans (by linarith)

end PhysicalTree

end
end LocalLaw
