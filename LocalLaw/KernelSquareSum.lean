import LocalLaw.OutsideBallKernelSum
import LocalLaw.LocalizationErrorBounds
import LocalLaw.ComponentFiniteLocalization

/-!
# Finite squared-kernel sums from actual sphere counts

At critical transfer squared decay cancels the d-1 sphere growth exactly.
The sum therefore costs only the number of actual distance layers. These
bounds provide the squared-weight budget in local boundary concentration.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance kernelSquareSumDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) canonicalKernelSquareComponentMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem connected_critical_square_kernel_sum (G : SimpleGraph V) (hG : G.Connected)
    (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, G.degree v ≤ d) (o : V) (R : ℕ)
    (hR : ∀ v, G.dist o v ≤ R) :
    (∑ v, (((d : ℝ) - 1) ^ G.dist o v)⁻¹) ≤ 2 * ((R : ℝ) + 1) := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hk : 0 < (d : ℝ) - 1 := by linarith
  have hmaps : ∀ v ∈ (Finset.univ : Finset V), G.dist o v ∈ Finset.range (R + 1) := by
    intro v _
    exact Finset.mem_range.mpr (by have hh := hR v; omega)
  have hsplit := (Finset.sum_fiberwise_of_maps_to hmaps
    (fun v => (((d : ℝ) - 1) ^ G.dist o v)⁻¹)).symm
  have hper : ∀ n : ℕ,
      (∑ v ∈ Finset.univ.filter (fun v => G.dist o v = n),
        (((d : ℝ) - 1) ^ G.dist o v)⁻¹) ≤ 2 := by
    intro n
    calc
      _ = ∑ _v ∈ Finset.univ.filter (fun v => G.dist o v = n), (((d : ℝ) - 1) ^ n)⁻¹ := by
        exact Finset.sum_congr rfl (fun v hv => by rw [(Finset.mem_filter.mp hv).2])
      _ = ((Finset.univ.filter (fun v => G.dist o v = n)).card : ℝ) * (((d : ℝ) - 1) ^ n)⁻¹ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * ((d : ℝ) - 1) ^ n) * (((d : ℝ) - 1) ^ n)⁻¹ :=
        mul_le_mul_of_nonneg_right (connected_dist_sphere_card G hG d hd hdegree o n) (by positivity)
      _ = 2 := by field_simp
  calc
    _ = ∑ n ∈ Finset.range (R + 1),
        ∑ v ∈ Finset.univ.filter (fun v => G.dist o v = n), (((d : ℝ) - 1) ^ G.dist o v)⁻¹ := hsplit
    _ ≤ ∑ _n ∈ Finset.range (R + 1), (2 : ℝ) := Finset.sum_le_sum (fun n _ => hper n)
    _ = _ := by simp; ring

theorem connected_decaying_kernel_square_sum (G : SimpleGraph V) (hG : G.Connected)
    (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, G.degree v ≤ d) (z : ℂ)
    (K : Matrix V V ℂ) (C : ℝ) (_hC : 0 ≤ C) (o : V) (R : ℕ)
    (hR : ∀ v, G.dist o v ≤ R)
    (hkernel : ∀ v, ‖K o v‖ ≤ C * physicalTransfer d z ^ G.dist o v) :
    (∑ v, ‖K o v‖ ^ 2) ≤ 2 * C ^ 2 * ((R : ℝ) + 1) := by
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hentry (v : V) : ‖K o v‖ ^ 2 ≤ C ^ 2 * (((d : ℝ) - 1) ^ G.dist o v)⁻¹ := by
    have hsq := pow_le_pow_left₀ (norm_nonneg (K o v)) (hkernel v) 2
    have htail := physical_transfer_two_sided_tail d hd z (G.dist o v)
    rw [hcast] at htail
    calc
      _ ≤ (C * physicalTransfer d z ^ G.dist o v) ^ 2 := hsq
      _ = C ^ 2 * physicalTransfer d z ^ (2 * G.dist o v) := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm (G.dist o v) 2]
      _ ≤ _ := mul_le_mul_of_nonneg_left htail (sq_nonneg C)
  calc
    _ ≤ ∑ v, C ^ 2 * (((d : ℝ) - 1) ^ G.dist o v)⁻¹ := Finset.sum_le_sum (fun v _ => hentry v)
    _ = C ^ 2 * ∑ v, (((d : ℝ) - 1) ^ G.dist o v)⁻¹ := (Finset.mul_sum ..).symm
    _ ≤ C ^ 2 * (2 * ((R : ℝ) + 1)) := mul_le_mul_of_nonneg_left
      (connected_critical_square_kernel_sum G hG d hd hdegree o R hR) (sq_nonneg C)
    _ = _ := by ring

namespace DeficientGraph
variable {A : Type} [Fintype A] [DecidableEq A] {d : ℕ}

theorem finite_extensionGreen_square_sum (g : DeficientGraph A d) (hd : 3 ≤ d)
    (hG : g.graph.Connected) (hbudget : g.FiniteReferenceBudget)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (R : ℕ)
    (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2) (i : A) :
    (∑ j, ‖g.extensionGreen q z i j‖ ^ 2) ≤
      8 * finiteExtraReferenceConstant d ^ 2 * ((R : ℝ) + 1) := by
  have hC : 0 ≤ 2 * finiteExtraReferenceConstant d := by
    have hh := finiteExtraReferenceConstant_ge_one d hd
    linarith
  have hh := connected_decaying_kernel_square_sum g.graph hG d hd g.degree_le z
    (g.extensionGreen q z) (2 * finiteExtraReferenceConstant d) hC i R (hR i)
    (fun j => by simpa only [referenceDecay] using
      g.finite_class_kernel_bound hd hG hbudget z q hz hq R hR small i j)
  convert hh using 1
  ring

/-- The same logarithmic squared-row bound holds for disconnected models;
only the root component contributes. -/
theorem componentwise_extensionGreen_square_sum (g : DeficientGraph A d) (hd : 3 ≤ d)
    (hbudget : g.ComponentFiniteReferenceBudget)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (R : ℕ)
    (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2) (i : A) :
    (∑ j, ‖g.extensionGreen q z i j‖ ^ 2) ≤
      8 * finiteExtraReferenceConstant d ^ 2 * ((R : ℝ) + 1) := by
  let c := g.graph.connectedComponentMk i
  let gc := g.restrict c.supp
  have hdiam : ∀ a b, gc.graph.dist a b ≤ R := by
    intro a b
    change (g.graph.induce c.supp).dist a b ≤ R
    rw [isolated_induce_distance g.graph c.supp (g.component_cut c)]
    exact hR a.val b.val
  have hh := gc.finite_extensionGreen_square_sum hd c.connected_induce_supp (hbudget c)
    z q hz hq R hdiam small ⟨i, rfl⟩
  rw [g.restrict_extensionGreen_of_isolated hd c.supp (g.component_cut c) q z hz hq] at hh
  simp only [Matrix.submatrix_apply] at hh
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun j : A => j ∈ c.supp)
    (fun j => ‖g.extensionGreen q z i j‖ ^ 2)
  have hzero : (∑ j : {j : A // j ∉ c.supp}, ‖g.extensionGreen q z i j.val‖ ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [g.extensionGreen_zero_across_cut hd c.supp (g.component_cut c) q z hz hq i rfl j.val j.property]
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0)]
  rw [hzero, add_zero] at hsplit
  exact hsplit ▸ hh

end DeficientGraph

end LocalLaw
