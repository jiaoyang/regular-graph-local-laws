import SpectralConsequences.KestenMcKayCDF
import SpectralConsequences.QuantileRigidity

/-! # Actual source classical eigenvalue locations and their endpoint -/

open Set MeasureTheory
noncomputable section
namespace SpectralConsequences

def classicalLocation (d : ℕ) (hd : 3 ≤ d) {N : ℕ} (i : Fin N) : ℝ :=
  (kestenMcKayCompactCDF d hd).quantile i

theorem classicalLocation_mem (d : ℕ) (hd : 3 ≤ d) {N : ℕ} (i : Fin N) :
    classicalLocation d hd i ∈ Icc (-2 : ℝ) 2 :=
  (kestenMcKayCompactCDF d hd).quantile_mem i

theorem cdf_classicalLocation (d : ℕ) (hd : 3 ≤ d) {N : ℕ} (i : Fin N) :
    kestenMcKayCDF d (classicalLocation d hd i)=sourceQuantileLevel i :=
  (kestenMcKayCompactCDF d hd).cdf_quantile i

theorem one_sub_sourceQuantileLevel {N : ℕ} (i : Fin N) :
    1-sourceQuantileLevel i=((i.val : ℝ)+1)/(N : ℝ) := by
  have hi := i.is_lt
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnum : ((N-1-i.val : ℕ) : ℝ)+(i.val : ℝ)+1=(N : ℝ) := by
    exact_mod_cast (show N-1-i.val+i.val+1=N by omega)
  unfold sourceQuantileLevel
  field_simp [hN]
  linarith

/-- This is exactly the paper's tail equation i/N, with zero-based index i. -/
theorem classicalLocation_tail_integral (d : ℕ) (hd : 3 ≤ d) {N : ℕ} (i : Fin N) :
    (∫x in classicalLocation d hd i..2,LocalLaw.kestenMcKayDensity d x)=
      ((i.val : ℝ)+1)/(N : ℝ) := by
  have hmem := classicalLocation_mem d hd i
  have hh := kestenMcKayCDF_sub d hd hmem.1 hmem.2 (le_refl (2 : ℝ))
  rw [kestenMcKayCDF_above d hd 2 le_rfl,cdf_classicalLocation] at hh
  exact hh.symm.trans (one_sub_sourceQuantileLevel i)

theorem kestenMcKayCDF_injectiveOn (d : ℕ) (hd : 3 ≤ d) :
    InjOn (kestenMcKayCDF d) (Icc (-2 : ℝ) 2) := by
  intro x hx y hy hxy
  have hh := (kestenMcKaySquareRootCDF d hd).inverse_modulus x y 0 hx hy le_rfl
    (show |kestenMcKayCDF d x-kestenMcKayCDF d y| ≤ 0 by rw [hxy,sub_self,abs_zero])
  have hdist : |x-y| ≤ 0 := by
    simpa only [zero_div,Real.zero_rpow (by norm_num : (2/3 : ℝ) ≠ 0)] using hh
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hdist (abs_nonneg _)))

theorem classicalLocation_last (d : ℕ) (hd : 3 ≤ d) (n : ℕ) :
    classicalLocation d hd (Fin.last n)=(-2 : ℝ) := by
  apply kestenMcKayCDF_injectiveOn d hd (classicalLocation_mem d hd _) (by norm_num)
  rw [cdf_classicalLocation,kestenMcKayCDF_below d (-2) le_rfl]
  simp [sourceQuantileLevel]

end SpectralConsequences
