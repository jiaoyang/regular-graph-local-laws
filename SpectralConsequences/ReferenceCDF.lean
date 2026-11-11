import SpectralConsequences.EmpiricalCDF
import Mathlib.Topology.Order.IntermediateValue

/-! # A compact continuous reference CDF and its actual classical locations -/

open Set
noncomputable section
namespace SpectralConsequences

structure CompactCDF where
  lower : ℝ
  upper : ℝ
  proper : lower < upper
  cdf : ℝ → ℝ
  continuous : Continuous cdf
  monotone : Monotone cdf
  below : ∀ x, x ≤ lower → cdf x = 0
  above : ∀ x, upper ≤ x → cdf x = 1

namespace CompactCDF

def clip (P : CompactCDF) (x : ℝ) : ℝ := max P.lower (min P.upper x)

theorem clip_mem (P : CompactCDF) (x : ℝ) : P.clip x ∈ Icc P.lower P.upper :=
  ⟨le_max_left _ _,max_le P.proper.le (min_le_left _ _)⟩

theorem clip_eq (P : CompactCDF) {x : ℝ} (hx : x ∈ Icc P.lower P.upper) :
    P.clip x = x := by
  simp only [clip,min_eq_right hx.2,max_eq_right hx.1]

theorem cdf_clip (P : CompactCDF) (x : ℝ) : P.cdf (P.clip x) = P.cdf x := by
  by_cases hlow : x ≤ P.lower
  · have hc : P.clip x = P.lower := by
      simp only [clip,min_eq_right (hlow.trans P.proper.le),max_eq_left hlow]
    rw [hc,P.below _ le_rfl,P.below _ hlow]
  by_cases hupp : P.upper ≤ x
  · have hc : P.clip x = P.upper := by
      simp only [clip,min_eq_left hupp,max_eq_right P.proper.le]
    rw [hc,P.above _ le_rfl,P.above _ hupp]
  rw [P.clip_eq ⟨(le_of_not_ge hlow),(le_of_not_ge hupp)⟩]

theorem cdf_nonnegative (P : CompactCDF) (x : ℝ) : 0 ≤ P.cdf x := by
  by_cases h : x ≤ P.lower
  · rw [P.below _ h]
  · have hh := P.monotone (le_of_not_ge h)
    rwa [P.below _ le_rfl] at hh

theorem cdf_le_one (P : CompactCDF) (x : ℝ) : P.cdf x ≤ 1 := by
  by_cases h : P.upper ≤ x
  · rw [P.above _ h]
  · have hh := P.monotone (le_of_not_ge h)
    rwa [P.above _ le_rfl] at hh

theorem exists_value (P : CompactCDF) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    ∃ x, x ∈ Icc P.lower P.upper ∧ P.cdf x = u := by
  have hmem : u ∈ Icc (P.cdf P.lower) (P.cdf P.upper) := by
    simpa only [P.below _ le_rfl,P.above _ le_rfl] using hu
  exact intermediate_value_Icc P.proper.le P.continuous.continuousOn hmem

end CompactCDF

theorem sourceQuantileLevel_mem {N : ℕ} (i : Fin N) :
    sourceQuantileLevel i ∈ Icc (0 : ℝ) 1 := by
  have hN : 0 < N := by have hi := i.is_lt; omega
  constructor
  · unfold sourceQuantileLevel
    positivity
  · apply (div_le_one (Nat.cast_pos.mpr hN)).mpr
    exact_mod_cast (show N-1-i.val ≤ N by omega)

namespace CompactCDF

def quantile (P : CompactCDF) {N : ℕ} (i : Fin N) : ℝ :=
  Classical.choose (P.exists_value (sourceQuantileLevel i) (sourceQuantileLevel_mem i))

theorem quantile_mem (P : CompactCDF) {N : ℕ} (i : Fin N) :
    P.quantile i ∈ Icc P.lower P.upper :=
  (Classical.choose_spec (P.exists_value (sourceQuantileLevel i) (sourceQuantileLevel_mem i))).1

theorem cdf_quantile (P : CompactCDF) {N : ℕ} (i : Fin N) :
    P.cdf (P.quantile i) = sourceQuantileLevel i :=
  (Classical.choose_spec (P.exists_value (sourceQuantileLevel i) (sourceQuantileLevel_mem i))).2

/-- Confinement controls only the part removed by clamping. -/
theorem sub_clip_abs_le (P : CompactCDF) (x Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hlo : P.lower - Δ ≤ x) (hhi : x ≤ P.upper + Δ) : |x - P.clip x| ≤ Δ := by
  by_cases hx : x ≤ P.lower
  · have hc : P.clip x = P.lower := by
      simp only [clip,min_eq_right (hx.trans P.proper.le),max_eq_left hx]
    rw [hc,abs_of_nonpos (by linarith : x-P.lower ≤ 0)]
    linarith
  by_cases hy : P.upper ≤ x
  · have hc : P.clip x = P.upper := by
      simp only [clip,min_eq_left hy,max_eq_right P.proper.le]
    rw [hc,abs_of_nonneg (by linarith : 0 ≤ x-P.upper)]
    linarith
  rw [P.clip_eq ⟨le_of_not_ge hx,le_of_not_ge hy⟩,sub_self,abs_zero]
  exact hΔ

end CompactCDF
end SpectralConsequences
