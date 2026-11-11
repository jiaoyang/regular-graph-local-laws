import LocalLaw.TreeKernelConvolution
import LocalLaw.CycleArcGeometry

/-!
# Genuine finite-cycle reference inverse

The actual cycle adjacency and missing-degree boundary matrix are used.
An explicit cyclic geometric column is verified against its two neighbors
before the nonsingular finite inverse is identified.
-/

open scoped BigOperators Matrix
set_option maxHeartbeats 1000000

namespace LocalLaw
noncomputable section
local instance cycleKernelDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Cyclic periodization of the two arc powers on a cycle of length n+3. -/
def cycleKernelCandidate (n : ℕ) (p t : ℂ) (s : Fin (n + 3)) : ℂ :=
  p * (t ^ s.val + t ^ (n + 3 - s.val)) / (1 - t ^ (n + 3))

theorem cycle_prev_value (n : ℕ) (s : Fin (n + 3)) :
    (s - 1).val = if s.val = 0 then n + 2 else s.val - 1 := by
  split_ifs with h
  · have hs : s = 0 := Fin.ext h
    subst s
    rw [zero_sub, Fin.coe_neg, Fin.val_one]
    simp only [show n + 3 - 1 = n + 2 by omega, Nat.mod_eq_of_lt (by omega : n + 2 < n + 3)]
  · exact Fin.val_sub_one_of_ne_zero (by intro hs; exact h (congrArg Fin.val hs))

theorem cycle_next_value (n : ℕ) (s : Fin (n + 3)) :
    (s + 1).val = if s.val + 1 = n + 3 then 0 else s.val + 1 := by
  rw [Fin.val_add, Fin.val_one]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- A two-sided geometric wave satisfies the homogeneous second-order row
relation at all nonroot positions. -/
theorem cycle_wave_recurrence (ell s : ℕ) (hs : 1 ≤ s) (hsell : s < ell)
    (a α t : ℂ) (hrec : α * t ^ 2 + a * t + α = 0) :
    α * ((t ^ (s - 1) + t ^ (ell - (s - 1))) +
      (t ^ (s + 1) + t ^ (ell - (s + 1)))) + a * (t ^ s + t ^ (ell - s)) = 0 := by
  generalize hu : s - 1 = u
  generalize hv : ell - (s + 1) = v
  have hp₂ : t ^ (ell - u) = t ^ (v + 2) := by congr 1; omega
  have hp₃ : t ^ (s + 1) = t ^ (u + 2) := by congr 1; omega
  have hp₅ : t ^ s = t ^ (u + 1) := by congr 1; omega
  have hp₆ : t ^ (ell - s) = t ^ (v + 1) := by congr 1; omega
  rw [hp₂, hp₃, hp₅, hp₆]
  simp only [pow_add, pow_one]
  linear_combination (t ^ u + t ^ v) * hrec

/-- Root normalization of the periodic wave, with all scalar denominators
handled explicitly by the nonzero t hypothesis. -/
theorem cycle_wave_root (n : ℕ) (a α p t : ℂ) (ht : t ≠ 0)
    (hrec : α * t ^ 2 + a * t + α = 0)
    (hjump : p * α * (t ^ 2 - 1) = t) :
    p * (2 * α * (t + t ^ (n + 2)) + a * (1 + t ^ (n + 3))) = 1 - t ^ (n + 3) := by
  apply (mul_left_cancel₀ ht)
  have hj : p * α * (t ^ 2 - 1) - t = 0 := sub_eq_zero.mpr hjump
  rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
  linear_combination p * (1 + t ^ (n + 2) * t) * hrec + (1 - t ^ (n + 2) * t) * hj

/-- Complete row verification on the literal finite cycle. -/
theorem cycleKernelCandidate_row (n : ℕ) (a α p t : ℂ) (ht : t ≠ 0)
    (hden : 1 - t ^ (n + 3) ≠ 0)
    (hrec : α * t ^ 2 + a * t + α = 0)
    (hjump : p * α * (t ^ 2 - 1) = t) (s : Fin (n + 3)) :
    α * (cycleKernelCandidate n p t (s - 1) + cycleKernelCandidate n p t (s + 1)) +
      a * cycleKernelCandidate n p t s = (if s = 0 then (1 : ℂ) else 0) := by
  by_cases hs : s = 0
  · subst s
    simp only [cycleKernelCandidate, cycle_prev_value, cycle_next_value, Fin.val_zero,
      if_pos rfl, zero_add, show ¬ (1 = n + 3) by omega, if_false,
      Nat.sub_self, Nat.sub_zero, pow_zero]
    norm_num only [Pi.single_apply, if_pos rfl, one_ne_zero, one_add_one_eq_two]
    simp only [ite_true, Fin.val_one]
    have h₁ : n + 3 - (n + 2) = 1 := by omega
    have h₂ : n + 3 - 1 = n + 2 := by omega
    rw [h₁, h₂, pow_one]
    field_simp
    convert cycle_wave_root n a α p t ht hrec hjump using 1
    ring
  · have hsval : 1 ≤ s.val := by
      have hh : s.val ≠ 0 := by intro hv; exact hs (Fin.ext hv)
      omega
    have hnext : t ^ (s + 1).val + t ^ (n + 3 - (s + 1).val) =
        t ^ (s.val + 1) + t ^ (n + 3 - (s.val + 1)) := by
      rw [cycle_next_value]
      split_ifs with h
      · simp only [pow_zero, Nat.sub_zero, h, Nat.sub_self]
        ring
      · rfl
    have hprev : (s - 1).val = s.val - 1 := by rw [cycle_prev_value, if_neg (by omega)]
    simp only [cycleKernelCandidate, Pi.single_apply, if_neg hs]
    rw [hprev, hnext]
    have hh := cycle_wave_recurrence (n + 3) s.val hsval s.is_lt a α t hrec
    field_simp
    linear_combination p * hh

/-- The literal normalized cycle matrix, with the actual missing degree d-2. -/
def cycleReferenceMatrix (n d : ℕ) (m z : ℂ) : Matrix (Fin (n + 3)) (Fin (n + 3)) ℂ :=
  boundaryMatrix (normalizedAdjacency (SimpleGraph.cycleGraph (n + 3)) d)
    (Matrix.diagonal (fun _ => Complex.ofReal (((d : ℝ) - 2) / ((d : ℝ) - 1)))) m z

/-- This is precisely the graph's zero-deficit boundary reference model. -/
theorem cycleReferenceMatrix_eq_full (n d : ℕ) (root : Fin (n + 3)) (m z : ℂ) :
    cycleReferenceMatrix n d m z =
      forestReferenceMatrix (SimpleGraph.cycleGraph (n + 3)) d root 0 m z := by
  unfold cycleReferenceMatrix forestReferenceMatrix forestBoundaryCoefficient
  apply congrArg (fun D : Matrix (Fin (n + 3)) (Fin (n + 3)) ℂ =>
    boundaryMatrix (normalizedAdjacency (SimpleGraph.cycleGraph (n + 3)) d) D m z)
  apply congrArg Matrix.diagonal
  funext v
  simp only [Nat.cast_zero, ite_self, sub_zero]
  congr 4
  convert congrArg (fun x : ℕ => (x : ℝ))
    (SimpleGraph.cycleGraph_degree_three_le (n := n) (v := v)).symm using 1
  apply congrArg (fun x : ℕ => (x : ℝ))
  apply congrArg (fun inst => @SimpleGraph.degree _ _ v inst)
  exact Subsingleton.elim _ _

/-- Genuine nonsingularity of the actual cycle boundary model. -/
theorem cycleReferenceMatrix_isUnit (n d : ℕ) (hd : 3 ≤ d) (m z : ℂ)
    (hz : 0 < z.im) (hmim : 0 ≤ m.im) : IsUnit (cycleReferenceMatrix n d m z) := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  unfold cycleReferenceMatrix
  exact boundaryMatrix_isUnit (normalizedAdjacency (SimpleGraph.cycleGraph (n + 3)) d)
    (normalizedAdjacency_isHermitian _ d)
    (fun _ : Fin (n + 3) => ((d : ℝ) - 2) / ((d : ℝ) - 1))
    (fun _ => div_nonneg (by linarith) (by linarith)) m z hz hmim

/-- Actual two-neighbor row formula on the normalized finite cycle. -/
theorem cycleReferenceMatrix_mulVec (n d : ℕ) (m z : ℂ) (f : Fin (n + 3) → ℂ)
    (s : Fin (n + 3)) :
    (cycleReferenceMatrix n d m z *ᵥ f) s = treeEdgeWeight d * (f (s - 1) + f (s + 1)) +
      (-z - m * (((d : ℂ) - 2) / ((d : ℂ) - 1))) * f s := by
  unfold cycleReferenceMatrix boundaryMatrix spectralMatrix
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
    Matrix.smul_mulVec_assoc]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal]
  rw [normalizedAdjacency_mulVec_neighbor]
  have hset : (SimpleGraph.cycleGraph (n + 3)).neighborSet s = {s - 1, s + 1} := by
    convert (SimpleGraph.cycleGraph_neighborSet (n := n + 1) (v := s)) using 1
  simp only [SimpleGraph.neighborFinset, hset, Set.toFinset_insert, Set.toFinset_singleton]
  have hne : s - 1 ≠ s + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc s, left_eq_add]
    exact ne_of_beq_false rfl
  rw [Finset.sum_pair hne]
  simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_natCast,
    Complex.ofReal_ofNat, Complex.ofReal_one]
  ring

/-- Scalar homogeneous row relation from the semicircle quadratic. -/
theorem cycle_scalar_recurrence (d : ℕ) (hd : 3 ≤ d) (m z : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) :
    treeEdgeWeight d * (-m * treeEdgeWeight d) ^ 2 +
      (-z - m * (((d : ℂ) - 2) / ((d : ℂ) - 1))) * (-m * treeEdgeWeight d) + treeEdgeWeight d = 0 := by
  have hk : (d : ℂ) - 1 ≠ 0 := by
    have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
    intro heq
    have hh := congrArg Complex.re heq
    simp at hh
    linarith
  rw [mul_pow, neg_sq, treeEdgeWeight_sq d hd]
  field_simp
  linear_combination treeEdgeWeight d * ((d : ℂ) - 1) * hm

/-- Scalar root normalization for the regular-tree coefficient. -/
theorem cycle_scalar_jump (d : ℕ) (hd : 3 ≤ d) (m z : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hmim : 0 ≤ m.im) :
    kestenMcKayTransform d m z * treeEdgeWeight d * ((-m * treeEdgeWeight d) ^ 2 - 1) =
      -m * treeEdgeWeight d := by
  have hkcast : ((d - 1 : ℕ) : ℂ) = (d : ℂ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hsq : (-m * treeEdgeWeight d) ^ 2 = m ^ 2 / ((d - 1 : ℕ) : ℂ) := by
    rw [mul_pow, neg_sq, treeEdgeWeight_sq d hd, hkcast]
    ring
  have hden := kestenMcKay_algebraic_denominator_ne_zero d hd m z hm hz hmim
  have hc : kestenMcKayTransform d m z * (1 - (-m * treeEdgeWeight d) ^ 2) = m := by
    rw [hsq, kestenMcKayTransform_eq d hd m z hm hz hmim]
    exact div_mul_cancel₀ m hden
  linear_combination -treeEdgeWeight d * hc

/-- The physical cycle transfer rate is bounded away from one. -/
theorem cycle_transfer_norm_le_three_quarters (d : ℕ) (hd : 3 ≤ d) (m : ℂ) (hm : ‖m‖ ≤ 1) :
    ‖-m * treeEdgeWeight d‖ ≤ 3 / 4 := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hkpos : 0 < (d : ℝ) - 1 := by linarith
  have hsquare : ‖-m * treeEdgeWeight d‖ ^ 2 ≤ 1 / 2 := by
    rw [norm_mul, norm_neg, mul_pow, treeEdgeWeight_norm_sq d hd]
    have hm2 : ‖m‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hm
    calc
      _ ≤ 1 * (1 / ((d : ℝ) - 1)) := mul_le_mul_of_nonneg_right hm2 (by positivity)
      _ ≤ 1 / 2 := by rw [one_mul]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  nlinarith [norm_nonneg (-m * treeEdgeWeight d)]

/-- The cycle pole denominator has a uniform positive lower bound for every
length at least three. -/
theorem cycle_denominator_norm_lower (n d : ℕ) (hd : 3 ≤ d) (m : ℂ) (hm : ‖m‖ ≤ 1) :
    1 / 2 ≤ ‖1 - (-m * treeEdgeWeight d) ^ (n + 3)‖ := by
  have ht := cycle_transfer_norm_le_three_quarters d hd m hm
  have hp : ‖(-m * treeEdgeWeight d) ^ (n + 3)‖ ≤ (27 / 64 : ℝ) := by
    rw [norm_pow]
    calc
      _ ≤ (3 / 4 : ℝ) ^ (n + 3) := pow_le_pow_left₀ (norm_nonneg _) ht _
      _ ≤ (3 / 4 : ℝ) ^ 3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = _ := by norm_num
  have hh := norm_sub_norm_le (1 : ℂ) ((-m * treeEdgeWeight d) ^ (n + 3))
  rw [norm_one] at hh
  linarith

/-- The actual finite inverse equals the cyclic geometric kernel at every
pair of cycle vertices, with the difference taken modulo its literal length. -/
theorem cycleReferenceMatrix_inverse (n d : ℕ) (hd : 3 ≤ d) (m z : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) (hmnorm : ‖m‖ ≤ 1)
    (hz : 0 < z.im) (hmim : 0 ≤ m.im) (i j : Fin (n + 3)) :
    (cycleReferenceMatrix n d m z)⁻¹ i j =
      cycleKernelCandidate n (kestenMcKayTransform d m z) (-m * treeEdgeWeight d) (i - j) := by
  let t := -m * treeEdgeWeight d
  let p := kestenMcKayTransform d m z
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hα : treeEdgeWeight d ≠ 0 := by
    intro heq
    have hh := treeEdgeWeight_norm_sq d hd
    rw [heq, norm_zero, zero_pow (by norm_num)] at hh
    have hkpos : 0 < (d : ℝ) - 1 := by linarith
    have hp : (0 : ℝ) < 1 / ((d : ℝ) - 1) := by positivity
    linarith
  have ht : t ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (cavity_root_ne_zero hm)) hα
  have hden : 1 - t ^ (n + 3) ≠ 0 := by
    apply norm_pos_iff.mp
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (cycle_denominator_norm_lower n d hd m hmnorm)
  let f := fun s : Fin (n + 3) => cycleKernelCandidate n p t (s - j)
  have hAf : cycleReferenceMatrix n d m z *ᵥ f = Pi.single j 1 := by
    funext s
    rw [cycleReferenceMatrix_mulVec]
    have hh := cycleKernelCandidate_row n _ (treeEdgeWeight d) p t ht hden
      (cycle_scalar_recurrence d hd m z hm) (cycle_scalar_jump d hd m z hm hz hmim) (s - j)
    have hprev : (s - 1) - j = (s - j) - 1 := by abel
    have hnext : (s + 1) - j = (s - j) + 1 := by abel
    simpa only [f, hprev, hnext, Pi.single_apply, sub_eq_zero] using hh
  exact inverse_column_of_mulVec _ (cycleReferenceMatrix_isUnit n d hd m z hz hmim) f j hAf i

/-- The periodic numerator is symmetric under reversal of the cycle. -/
theorem cycleKernelCandidate_neg (n : ℕ) (p t : ℂ) (s : Fin (n + 3)) :
    cycleKernelCandidate n p t (-s) = cycleKernelCandidate n p t s := by
  by_cases hs : s = 0
  · simp only [hs, neg_zero]
  · have hsval : 0 < s.val := by
      have hh : s.val ≠ 0 := by intro hv; exact hs (Fin.ext hv)
      omega
    have hnval : (-s).val = n + 3 - s.val := by
      rw [Fin.coe_neg, Nat.mod_eq_of_lt (by omega)]
    have hsub : n + 3 - (n + 3 - s.val) = s.val := by omega
    simp only [cycleKernelCandidate, hnval, hsub]
    ring

/-- Root-zero row formula in the standard nonnegative cyclic coordinates. -/
theorem cycleReferenceMatrix_inverse_zero_row (n d : ℕ) (hd : 3 ≤ d) (m z : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) (hmnorm : ‖m‖ ≤ 1)
    (hz : 0 < z.im) (hmim : 0 ≤ m.im) (s : Fin (n + 3)) :
    (cycleReferenceMatrix n d m z)⁻¹ 0 s =
      kestenMcKayTransform d m z *
        ((-m * treeEdgeWeight d) ^ s.val + (-m * treeEdgeWeight d) ^ (n + 3 - s.val)) /
          (1 - (-m * treeEdgeWeight d) ^ (n + 3)) := by
  rw [cycleReferenceMatrix_inverse n d hd m z hm hmnorm hz hmim, zero_sub, cycleKernelCandidate_neg]
  rfl

/-- Exact physical cycle diagonal, including the full return factor. -/
theorem cycleReferenceMatrix_inverse_diagonal (n d : ℕ) (hd : 3 ≤ d) (z : ℂ)
    (hz : 0 < z.im) (i : Fin (n + 3)) :
    (cycleReferenceMatrix n d (semicircleRoot z) z)⁻¹ i i =
      kestenMcKayTransform d (semicircleRoot z) z *
        (1 + (-semicircleRoot z * treeEdgeWeight d) ^ (n + 3)) /
          (1 - (-semicircleRoot z * treeEdgeWeight d) ^ (n + 3)) := by
  rw [cycleReferenceMatrix_inverse n d hd (semicircleRoot z) z (semicircleRoot_equation z)
    (semicircleRoot_norm_le_one z) hz (semicircleRoot_im_pos hz).le, sub_self]
  simp only [cycleKernelCandidate, Fin.val_zero, pow_zero, Nat.sub_zero]

/-- Every full traversal of a physical cycle has norm at most one half. -/
theorem cycle_transfer_power_norm_le_half (n d : ℕ) (hd : 3 ≤ d) (m : ℂ) (hm : ‖m‖ ≤ 1) :
    ‖(-m * treeEdgeWeight d) ^ (n + 3)‖ ≤ 1 / 2 := by
  have ht := cycle_transfer_norm_le_three_quarters d hd m hm
  rw [norm_pow]
  calc
    _ ≤ (3 / 4 : ℝ) ^ (n + 3) := pow_le_pow_left₀ (norm_nonneg _) ht _
    _ ≤ (3 / 4 : ℝ) ^ 3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ ≤ 1 / 2 := by norm_num

/-- Genuine physical cycle inverse entries have a uniform graph-distance
kernel bound. Both cyclic arcs are derived from actual finite graph walks. -/
theorem cycleReferenceMatrix_inverse_decay (n d : ℕ) (hd : 3 ≤ d) (z : ℂ)
    (hz : 0 < z.im) (i j : Fin (n + 3)) :
    ‖(cycleReferenceMatrix n d (semicircleRoot z) z)⁻¹ i j‖ ≤
      8 * ‖-semicircleRoot z * treeEdgeWeight d‖ ^ (SimpleGraph.cycleGraph (n + 3)).dist i j := by
  let t := -semicircleRoot z * treeEdgeWeight d
  let p := kestenMcKayTransform d (semicircleRoot z) z
  let r := (i - j).val
  let dist := (SimpleGraph.cycleGraph (n + 3)).dist i j
  have ht0 : 0 ≤ ‖t‖ := norm_nonneg _
  have ht1 : ‖t‖ ≤ 1 := (cycle_transfer_norm_le_three_quarters d hd _ (semicircleRoot_norm_le_one z)).trans (by norm_num)
  have harcs := cycle_distance_le_arcs n j i
  have hdistcomm : (SimpleGraph.cycleGraph (n + 3)).dist j i = dist := SimpleGraph.dist_comm
  have hdist1 : dist ≤ r := by simpa only [hdistcomm] using harcs.1
  have hdist2 : dist ≤ n + 3 - r := by simpa only [hdistcomm] using harcs.2
  have hnum : ‖t ^ r + t ^ (n + 3 - r)‖ ≤ 2 * ‖t‖ ^ dist := by
    have h₁ := pow_le_pow_of_le_one ht0 ht1 hdist1
    have h₂ := pow_le_pow_of_le_one ht0 ht1 hdist2
    exact (norm_add_le _ _).trans (by simpa only [norm_pow] using (add_le_add h₁ h₂).trans_eq (by ring))
  have hden : 1 / 2 ≤ ‖1 - t ^ (n + 3)‖ :=
    cycle_denominator_norm_lower n d hd _ (semicircleRoot_norm_le_one z)
  have hp : ‖p‖ ≤ 2 := kestenMcKayTransform_norm_le_two d hd z hz
  rw [cycleReferenceMatrix_inverse n d hd (semicircleRoot z) z (semicircleRoot_equation z)
    (semicircleRoot_norm_le_one z) hz (semicircleRoot_im_pos hz).le]
  change ‖p * (t ^ r + t ^ (n + 3 - r)) / (1 - t ^ (n + 3))‖ ≤ 8 * ‖t‖ ^ dist
  rw [norm_div, norm_mul]
  calc
    _ ≤ (2 * (2 * ‖t‖ ^ dist)) / (1 / 2) :=
      div_le_div₀ (by positivity)
        (mul_le_mul hp hnum (norm_nonneg _) (by norm_num)) (by norm_num) hden
    _ = _ := by ring

/-- Direct bounded-domain lower bound for the actual regular-tree coefficient. -/
theorem kestenMcKay_bounded_norm_lower (d : ℕ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im)
    (B : ℝ) (hB : ‖z‖ ≤ B) :
    1 / (B + 2) ≤ ‖kestenMcKayTransform d (semicircleRoot z) z‖ := by
  let m := semicircleRoot z
  let q := (d : ℂ) / ((d - 1 : ℕ) : ℂ)
  let den := -z - q * m
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hkpos : 0 < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
  have hkcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hq : ‖q‖ ≤ 2 := by
    simp only [q, norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ hkpos).mpr
    rw [hkcast]
    linarith
  have hself : ‖q * m‖ ≤ 2 := by
    rw [norm_mul]
    exact (mul_le_mul hq (semicircleRoot_norm_le_one z) (norm_nonneg _) (by norm_num)).trans_eq (mul_one _)
  have hden : ‖den‖ ≤ B + 2 := by
    have hh := norm_sub_le (-z) (q * m)
    rw [norm_neg] at hh
    exact hh.trans (add_le_add hB hself)
  have hdenpos : 0 < ‖den‖ := norm_pos_iff.mpr
    (kestenMcKay_denominator_ne_zero d m z hz (semicircleRoot_im_pos hz).le)
  change 1 / (B + 2) ≤ ‖den⁻¹‖
  rw [norm_inv, ← one_div]
  exact one_div_le_one_div_of_le hdenpos hden

/-- Uniform upper and bounded-domain lower diagonal bounds for the actual
cycle inverse; the pole and numerator factors are both controlled explicitly. -/
theorem cycleReferenceMatrix_diagonal_norm_bounds (n d : ℕ) (hd : 3 ≤ d) (z : ℂ)
    (hz : 0 < z.im) (B : ℝ) (hB : ‖z‖ ≤ B) (i : Fin (n + 3)) :
    1 / (3 * (B + 2)) ≤ ‖(cycleReferenceMatrix n d (semicircleRoot z) z)⁻¹ i i‖ ∧
      ‖(cycleReferenceMatrix n d (semicircleRoot z) z)⁻¹ i i‖ ≤ 6 := by
  let T := (-semicircleRoot z * treeEdgeWeight d) ^ (n + 3)
  let p := kestenMcKayTransform d (semicircleRoot z) z
  have hT : ‖T‖ ≤ 1 / 2 := cycle_transfer_power_norm_le_half n d hd _ (semicircleRoot_norm_le_one z)
  have hplusLo : 1 / 2 ≤ ‖1 + T‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) (-T)
    simp only [norm_one, norm_neg, sub_neg_eq_add] at hh
    linarith
  have hplusHi : ‖1 + T‖ ≤ 3 / 2 := by
    have hh := norm_add_le (1 : ℂ) T
    rw [norm_one] at hh
    linarith
  have hminusLo : 1 / 2 ≤ ‖1 - T‖ := cycle_denominator_norm_lower n d hd _ (semicircleRoot_norm_le_one z)
  have hminusHi : ‖1 - T‖ ≤ 3 / 2 := by
    have hh := norm_sub_le (1 : ℂ) T
    rw [norm_one] at hh
    linarith
  have hBpos : 0 < B + 2 := by linarith [norm_nonneg z]
  have hpLo : 1 / (B + 2) ≤ ‖p‖ := kestenMcKay_bounded_norm_lower d hd z hz B hB
  have hpHi : ‖p‖ ≤ 2 := kestenMcKayTransform_norm_le_two d hd z hz
  rw [cycleReferenceMatrix_inverse_diagonal n d hd z hz i]
  change 1 / (3 * (B + 2)) ≤ ‖p * (1 + T) / (1 - T)‖ ∧ ‖p * (1 + T) / (1 - T)‖ ≤ 6
  rw [norm_div, norm_mul]
  constructor
  · calc
      _ = ((1 / (B + 2)) * (1 / 2)) / (3 / 2) := by field_simp; ring
      _ ≤ ‖p‖ * ‖1 + T‖ / ‖1 - T‖ :=
        div_le_div₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul hpLo hplusLo (by norm_num) (norm_nonneg _)) (by linarith) hminusHi
  · calc
      _ ≤ (2 * (3 / 2)) / (1 / 2) :=
        div_le_div₀ (by norm_num) (mul_le_mul hpHi hplusHi (norm_nonneg _) (by norm_num)) (by norm_num) hminusLo
      _ = 6 := by norm_num

end
end LocalLaw
