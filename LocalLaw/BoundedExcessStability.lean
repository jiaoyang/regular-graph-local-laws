import LocalLaw.CoreBoundaryConvolution
import LocalLaw.DeficientGraphModel
import LocalLaw.GoodThresholdOne

/-!
# Actual bounded-excess finite-model boundary perturbation

The reference entry bound is an explicit source reference-class input.
Convolution, positive kernels, uniform companion bounds, and genuine inverse
obligations are derived from the actual deficient graph and physical root.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw

def physicalTransfer (d : ℕ) (z : ℂ) : ℝ := ‖-semicircleRoot z * treeEdgeWeight d‖

theorem physicalTransfer_pos (d : ℕ) (hd : 3 ≤ d) (z : ℂ) : 0 < physicalTransfer d z := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hsq := treeEdgeWeight_norm_sq d hd
  have hinv : 0 < ((d : ℝ) - 1)⁻¹ := inv_pos.mpr (by linarith)
  have hspos : 0 < ‖treeEdgeWeight d‖ ^ 2 := by simpa only [hsq, one_div] using hinv
  have he : 0 < ‖treeEdgeWeight d‖ := by nlinarith [norm_nonneg (treeEdgeWeight d)]
  unfold physicalTransfer
  rw [norm_mul, norm_neg]
  exact mul_pos (norm_pos_iff.mpr (semicircleRoot_ne_zero z)) he

theorem physicalTransfer_sq_le_half (d : ℕ) (hd : 3 ≤ d) (z : ℂ) :
    physicalTransfer d z ^ 2 ≤ 1 / 2 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hh := cavity_transfer_norm_sq_bound d hd (semicircleRoot z) (semicircleRoot_norm_le_one z)
  have hrecip : ((d : ℝ) - 1)⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (show 2 ≤ (d : ℝ) - 1 by linarith)
  exact hh.trans hrecip

theorem linear_power_le_four (t : ℝ) (ht : 0 ≤ t) (ht34 : t ≤ 3 / 4) (n : ℕ) :
    ((n : ℝ) + 1) * t ^ n ≤ 4 := by
  have htone : t ≤ 1 := by linarith
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hm := mul_le_mul_of_nonneg_right ih ht
    have hp : t ^ (n + 1) ≤ 1 := pow_le_one₀ ht htone
    calc
      _ = (((n : ℝ) + 1) * t ^ n) * t + t ^ (n + 1) := by
        simp only [Nat.cast_add, Nat.cast_one, pow_succ]
        ring
      _ ≤ 4 * t + 1 := add_le_add hm hp
      _ ≤ 4 := by linarith

namespace DeficientGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

def referenceDecay (g : DeficientGraph V d) (z : ℂ) (i j : V) : ℝ :=
  physicalTransfer d z ^ g.graph.dist i j

def referenceCompanion (g : DeficientGraph V d) (z : ℂ) (i j : V) : ℝ :=
  ((g.graph.dist i j : ℝ) + 1) * g.referenceDecay z i j

omit [DecidableEq V] in
theorem referenceDecay_pos (g : DeficientGraph V d) (hd : 3 ≤ d) (z : ℂ) (i j : V) :
    0 < g.referenceDecay z i j := pow_pos (physicalTransfer_pos d hd z) _

omit [DecidableEq V] in
theorem referenceCompanion_pos (g : DeficientGraph V d) (hd : 3 ≤ d) (z : ℂ) (i j : V) :
    0 < g.referenceCompanion z i j :=
  mul_pos (by positivity) (g.referenceDecay_pos hd z i j)

omit [DecidableEq V] in
theorem referenceCompanion_le_four (g : DeficientGraph V d) (hd : 3 ≤ d) (z : ℂ) (i j : V) :
    g.referenceCompanion z i j ≤ 4 := by
  have ht := (physicalTransfer_pos d hd z).le
  have hs := physicalTransfer_sq_le_half d hd z
  have ht34 : physicalTransfer d z ≤ 3 / 4 := by nlinarith
  exact linear_power_le_four _ ht ht34 _

omit [DecidableEq V] in
theorem boundaryCoefficient_le_treeWeight (g : DeficientGraph V d) (hd : 3 ≤ d) (v : V) :
    g.boundaryCoefficient v ≤ treeBoundaryWeight g.graph d v := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  unfold boundaryCoefficient treeBoundaryWeight
  apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ (d : ℝ) - 1)
  have hδ : (0 : ℝ) ≤ g.deficit v := Nat.cast_nonneg _
  linarith

/-- Deficits only decrease the nonnegative boundary coefficient, so the
actual geometry-only B.6 bound supplies this model's convolution automatically. -/
theorem referenceDecay_convolution (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected) (ω : ℕ) (hω : graphExcess g.graph ≤ ω) (z : ℂ) (i j : V) :
    (∑ v : V, g.boundaryCoefficient v * g.referenceDecay z i v * g.referenceDecay z v j) ≤
      coreConvolutionConstant ω * g.referenceCompanion z i j := by
  have hh := cavity_power_boundary_convolution g.graph hG ω hω d hd g.degree_le
    (semicircleRoot z) (semicircleRoot_norm_le_one z) i j
  calc
    _ ≤ ∑ v : V, treeBoundaryWeight g.graph d v * g.referenceDecay z i v * g.referenceDecay z v j := by
      apply Finset.sum_le_sum
      intro v _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (g.boundaryCoefficient_le_treeWeight hd v)
          (g.referenceDecay_pos hd z i v).le) (g.referenceDecay_pos hd z v j).le
    _ ≤ _ := by simpa only [referenceDecay, referenceCompanion, physicalTransfer, mul_assoc] using hh

omit [DecidableEq V] in
theorem referenceCompanion_diameter_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (z : ℂ) (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R) (i j : V) :
    g.referenceCompanion z i j ≤ ((R : ℝ) + 1) * g.referenceDecay z i j := by
  apply mul_le_mul_of_nonneg_right _ (g.referenceDecay_pos hd z i j).le
  exact add_le_add_right (Nat.cast_le.mpr (hR i j)) 1

/-- Finite-model Proposition-2.12 perturbation from a source reference entry
bound. The actual convolution and genuine matrix units are conclusions of
earlier graph theorems, not additional inputs here. -/
theorem reference_boundary_stability (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected) (ω : ℕ) (hω : graphExcess g.graph ≤ ω)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (C : ℝ) (hC : 0 ≤ C) (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (reference : ∀ i j, ‖g.extensionGreen (semicircleRoot z) z i j‖ ≤ C * g.referenceDecay z i j)
    (small : ‖q - semicircleRoot z‖ * C * coreConvolutionConstant ω * ((R : ℝ) + 1) ≤ 1 / 2)
    (i j : V) :
    ‖g.extensionGreen q z i j - g.extensionGreen (semicircleRoot z) z i j‖ ≤
      2 * ‖q - semicircleRoot z‖ * C ^ 2 * coreConvolutionConstant ω * g.referenceCompanion z i j ∧
      ‖g.extensionGreen q z i j‖ ≤ 2 * C * g.referenceDecay z i j := by
  have hunitq := g.extensionMatrix_isUnit hd q z hz hq
  have hunitm := g.extensionMatrix_isUnit hd (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le
  exact boundary_kernel_stability g.H g.boundaryCoefficient q (semicircleRoot z) z hunitq hunitm
    (g.referenceDecay z) (g.referenceCompanion z) C (coreConvolutionConstant ω) ((R : ℝ) + 1)
    (g.boundaryCoefficient_nonnegative hd) (fun a b => (g.referenceDecay_pos hd z a b).le)
    (g.referenceCompanion_pos hd z) hC (coreConvolutionConstant_nonnegative ω) (by positivity)
    reference (g.referenceCompanion_diameter_bound hd z R hR)
    (g.referenceDecay_convolution hd hG ω hω z) small i j

/-- Uniform reference sensitivity is derived from the companion bound four. -/
theorem reference_boundary_uniform_stability (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected) (ω : ℕ) (hω : graphExcess g.graph ≤ ω)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (C : ℝ) (hC : 0 ≤ C) (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (reference : ∀ i j, ‖g.extensionGreen (semicircleRoot z) z i j‖ ≤ C * g.referenceDecay z i j)
    (small : ‖q - semicircleRoot z‖ * C * coreConvolutionConstant ω * ((R : ℝ) + 1) ≤ 1 / 2)
    (i j : V) :
    ‖g.extensionGreen q z i j - g.extensionGreen (semicircleRoot z) z i j‖ ≤
      (8 * C ^ 2 * coreConvolutionConstant ω) * ‖q - semicircleRoot z‖ := by
  have h := (g.reference_boundary_stability hd hG ω hω z q hz hq C hC R hR reference small i j).1
  have hC0 := coreConvolutionConstant_nonnegative ω
  have hb := mul_le_mul_of_nonneg_left (g.referenceCompanion_le_four hd z i j)
    (by positivity : 0 ≤ 2 * ‖q - semicircleRoot z‖ * C ^ 2 * coreConvolutionConstant ω)
  exact h.trans (hb.trans_eq (by ring))

/-- Two perturbed boundary values satisfy an order-one Lipschitz bound,
derived from the actual graph convolution and the same explicit feedback budget. -/
theorem reference_boundary_uniform_lipschitz (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected) (ω : ℕ) (hω : graphExcess g.graph ≤ ω)
    (z q v : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (hv : 0 ≤ v.im)
    (C : ℝ) (hC : 0 ≤ C) (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (reference : ∀ i j, ‖g.extensionGreen (semicircleRoot z) z i j‖ ≤ C * g.referenceDecay z i j)
    (smallq : ‖q - semicircleRoot z‖ * C * coreConvolutionConstant ω * ((R : ℝ) + 1) ≤ 1 / 2)
    (smallv : ‖v - semicircleRoot z‖ * C * coreConvolutionConstant ω * ((R : ℝ) + 1) ≤ 1 / 2)
    (i j : V) :
    ‖g.extensionGreen q z i j - g.extensionGreen v z i j‖ ≤
      (16 * C ^ 2 * coreConvolutionConstant ω) * dist q v := by
  have hunitq := g.extensionMatrix_isUnit hd q z hz hq
  have hunitv := g.extensionMatrix_isUnit hd v z hz hv
  have hunitm := g.extensionMatrix_isUnit hd (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le
  have h := boundary_kernel_uniform_lipschitz g.H g.boundaryCoefficient q v (semicircleRoot z) z
    hunitq hunitv hunitm (g.referenceDecay z) (g.referenceCompanion z) C
    (coreConvolutionConstant ω) ((R : ℝ) + 1) 4
    (g.boundaryCoefficient_nonnegative hd) (fun a b => (g.referenceDecay_pos hd z a b).le)
    (g.referenceCompanion_pos hd z) hC (coreConvolutionConstant_nonnegative ω) (by positivity)
    reference (g.referenceCompanion_diameter_bound hd z R hR)
    (g.referenceDecay_convolution hd hG ω hω z) (g.referenceCompanion_le_four hd z)
    smallq smallv i j
  exact h.trans_eq (by ring)

/-- At total deficit plus excess at most one, the reference estimate is
proved by the tree/unicyclic classification and is no longer an input. -/
theorem reference_one_boundary_uniform_stability (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected) (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ 1)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * 8 * coreConvolutionConstant 1 * ((R : ℝ) + 1) ≤ 1 / 2)
    (i j : V) :
    ‖g.extensionGreen q z i j - g.extensionGreen (semicircleRoot z) z i j‖ ≤
      (8 * 8 ^ 2 * coreConvolutionConstant 1) * ‖q - semicircleRoot z‖ := by
  have hω : graphExcess g.graph ≤ 1 := by omega
  exact g.reference_boundary_uniform_stability hd hG 1 hω z q hz hq 8 (by norm_num) R hR
    (g.reference_one_entry_bound hd hG hbudget z hz) small i j

/-- The actual threshold-one model has the source diagonal variance cap:
its physical-reference imaginary part plus a uniform boundary correction. -/
theorem reference_one_boundary_im_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected) (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ 1)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * 8 * coreConvolutionConstant 1 * ((R : ℝ) + 1) ≤ 1 / 2)
    (i j : V) :
    |(g.extensionGreen q z i j).im| ≤
      192 * (kestenMcKayTransform d (semicircleRoot z) z).im +
        (8 * 8 ^ 2 * coreConvolutionConstant 1) * ‖q - semicircleRoot z‖ := by
  have hdiff := g.reference_one_boundary_uniform_stability hd hG hbudget z q hz hq R hR small i j
  have href := g.reference_one_im_md_bound hd hG hbudget z hz i j
  have him := Complex.abs_im_le_norm (g.extensionGreen q z i j -
    g.extensionGreen (semicircleRoot z) z i j)
  have hsplit : |(g.extensionGreen q z i j).im| ≤
      |(g.extensionGreen (semicircleRoot z) z i j).im| +
        |(g.extensionGreen q z i j - g.extensionGreen (semicircleRoot z) z i j).im| := by
    simp only [Complex.sub_im]
    have hh := abs_add_le ((g.extensionGreen q z i j).im -
      (g.extensionGreen (semicircleRoot z) z i j).im)
      (g.extensionGreen (semicircleRoot z) z i j).im
    rw [sub_add_cancel] at hh
    linarith
  exact hsplit.trans (add_le_add href (him.trans hdiff))

/-- Uniform sensitivity between two boundary values also follows without
any separate reference-class or convolution hypothesis at threshold one. -/
theorem reference_one_boundary_uniform_lipschitz (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected) (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ 1)
    (z q v : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (hv : 0 ≤ v.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (smallq : ‖q - semicircleRoot z‖ * 8 * coreConvolutionConstant 1 * ((R : ℝ) + 1) ≤ 1 / 2)
    (smallv : ‖v - semicircleRoot z‖ * 8 * coreConvolutionConstant 1 * ((R : ℝ) + 1) ≤ 1 / 2)
    (i j : V) :
    ‖g.extensionGreen q z i j - g.extensionGreen v z i j‖ ≤
      (16 * 8 ^ 2 * coreConvolutionConstant 1) * dist q v := by
  have hω : graphExcess g.graph ≤ 1 := by omega
  exact g.reference_boundary_uniform_lipschitz hd hG 1 hω z q v hz hq hv 8 (by norm_num) R hR
    (g.reference_one_entry_bound hd hG hbudget z hz) smallq smallv i j

end DeficientGraph
end LocalLaw
