import Mathlib

/-!
# Summing a decay kernel from bounded distance layers

A finite set with at most A vertices in each distance layer has a two-point
kernel sum bounded by 2*A*(distance+1)*t^distance for t^2<=1/2. Both the low
layers and the geometric tail are summed explicitly. This is the numerical
part of the bounded-excess core convolution argument.
-/

open scoped BigOperators
namespace LocalLaw

/-- The triangle inequalities force this minimum exponent in layer a. -/
def radialExponent (n a : ℕ) : ℕ := if a ≤ n then n else n + 2 * (a - n)

theorem radialExponent_le (n a e : ℕ) (hne : n ≤ e) (hae : 2 * a ≤ e + n) :
    radialExponent n a ≤ e := by
  unfold radialExponent
  split_ifs <;> omega

theorem radialExponent_high (n k : ℕ) : radialExponent n (n + 1 + k) = n + 2 * (k + 1) := by
  unfold radialExponent
  rw [if_neg (by omega)]
  congr 1
  omega

/-- A finite geometric sum at ratio at most one half is at most two. -/
theorem finite_geometric_le_two (x : ℝ) (M : ℕ) (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    (∑ k ∈ Finset.range M, x ^ k) ≤ 2 := by
  have hnonneg : 0 ≤ ∑ k ∈ Finset.range M, x ^ k := Finset.sum_nonneg (fun _ _ => pow_nonneg hx _)
  have hid := geom_sum_mul_neg x M
  have hpower := pow_nonneg hx M
  have hproduct := mul_le_mul_of_nonneg_left hxhalf hnonneg
  nlinarith

/-- Sum all radial layers through an arbitrary finite cutoff. -/
theorem radial_kernel_range_sum (n M : ℕ) (t : ℝ) (ht : 0 ≤ t) (htsq : t ^ 2 ≤ 1 / 2) :
    (∑ a ∈ Finset.range (n + 1 + M), t ^ radialExponent n a) ≤ ((n : ℝ) + 2) * t ^ n := by
  have hgeom := finite_geometric_le_two (t ^ 2) M (sq_nonneg _) htsq
  have hgeom0 : 0 ≤ ∑ k ∈ Finset.range M, (t ^ 2) ^ k := by positivity
  have htail : t ^ 2 * (∑ k ∈ Finset.range M, (t ^ 2) ^ k) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hgeom (sq_nonneg t)
    nlinarith
  have hlow : (∑ a ∈ Finset.range (n + 1), t ^ radialExponent n a) = ((n : ℝ) + 1) * t ^ n := by
    calc
      _ = ∑ _a ∈ Finset.range (n + 1), t ^ n := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [radialExponent, if_pos (by have hh := Finset.mem_range.mp ha; omega)]
      _ = _ := by simp [nsmul_eq_mul]
  have hhigh : (∑ k ∈ Finset.range M, t ^ radialExponent n (n + 1 + k)) =
      t ^ n * (t ^ 2 * ∑ k ∈ Finset.range M, (t ^ 2) ^ k) := by
    simp_rw [radialExponent_high]
    calc
      _ = ∑ k ∈ Finset.range M, (t ^ n * t ^ 2) * (t ^ 2) ^ k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [pow_add, show 2 * (k + 1) = 2 * k + 2 by omega, pow_add, pow_mul]
        ring
      _ = _ := by rw [← Finset.mul_sum]; ring
  rw [Finset.sum_range_add, hlow, hhigh]
  have hscaled := mul_le_mul_of_nonneg_left htail (pow_nonneg ht n)
  nlinarith

/-- Finite two-point kernel bound from actual layer counts and triangle
inequalities. No final convolution estimate is a hypothesis. -/
theorem radial_kernel_finset_sum {V : Type*} [DecidableEq V]
    (C : Finset V) (depth exponent : V → ℕ) (n A : ℕ) (t : ℝ)
    (ht : 0 ≤ t) (htone : t ≤ 1) (htsq : t ^ 2 ≤ 1 / 2)
    (layers : ∀ k : ℕ, (C.filter (fun v => depth v = k)).card ≤ A)
    (triangles : ∀ v ∈ C, n ≤ exponent v ∧ 2 * depth v ≤ exponent v + n) :
    (∑ v ∈ C, t ^ exponent v) ≤ 2 * (A : ℝ) * ((n : ℝ) + 1) * t ^ n := by
  classical
  let M := C.sup depth + 1
  have hmap : ∀ v ∈ C, depth v ∈ Finset.range (n + 1 + M) := by
    intro v hv
    have hh : depth v ≤ C.sup depth := Finset.le_sup hv
    apply Finset.mem_range.mpr
    dsimp [M]
    omega
  have hsum : (∑ v ∈ C, t ^ exponent v) =
      ∑ k ∈ Finset.range (n + 1 + M), ∑ v ∈ C.filter (fun v => depth v = k), t ^ exponent v :=
    (Finset.sum_fiberwise_of_maps_to hmap (fun v => t ^ exponent v)).symm
  have hper : ∀ k : ℕ, (∑ v ∈ C.filter (fun v => depth v = k), t ^ exponent v) ≤
      (A : ℝ) * t ^ radialExponent n k := by
    intro k
    calc
      _ ≤ ∑ _v ∈ C.filter (fun v => depth v = k), t ^ radialExponent n k := by
        apply Finset.sum_le_sum
        intro v hv
        obtain ⟨hvC, hvk⟩ := Finset.mem_filter.mp hv
        have hexp := radialExponent_le n (depth v) (exponent v) (triangles v hvC).1 (triangles v hvC).2
        rw [hvk] at hexp
        exact pow_le_pow_of_le_one ht htone hexp
      _ = ((C.filter (fun v => depth v = k)).card : ℝ) * t ^ radialExponent n k := by simp [nsmul_eq_mul]
      _ ≤ (A : ℝ) * t ^ radialExponent n k :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (layers k)) (pow_nonneg ht _)
  calc
    _ = _ := hsum
    _ ≤ ∑ k ∈ Finset.range (n + 1 + M), (A : ℝ) * t ^ radialExponent n k :=
      Finset.sum_le_sum (fun k _ => hper k)
    _ = (A : ℝ) * ∑ k ∈ Finset.range (n + 1 + M), t ^ radialExponent n k := (Finset.mul_sum ..).symm
    _ ≤ (A : ℝ) * (((n : ℝ) + 2) * t ^ n) :=
      mul_le_mul_of_nonneg_left (radial_kernel_range_sum n M t ht htsq) (Nat.cast_nonneg A)
    _ ≤ 2 * (A : ℝ) * ((n : ℝ) + 1) * t ^ n := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      have hconstant : (n : ℝ) + 2 ≤ 2 * ((n : ℝ) + 1) := by linarith
      have hh := mul_le_mul_of_nonneg_left hconstant (Nat.cast_nonneg A : (0 : ℝ) ≤ A)
      nlinarith [mul_le_mul_of_nonneg_right hh (pow_nonneg ht n)]

end LocalLaw
