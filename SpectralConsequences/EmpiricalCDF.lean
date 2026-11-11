import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Ordered empirical distributions with all multiplicities retained -/

open Filter Set
open scoped Topology
noncomputable section
namespace SpectralConsequences
local instance empiricalCDFDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def empiricalCDF {N : ℕ} (values : Fin N → ℝ) (E : ℝ) : ℝ :=
  ((Finset.univ.filter (fun j => values j ≤ E)).card : ℝ) / (N : ℝ)

/-- The article's one-based level (N-i)/N in zero-based Lean indexing. -/
def sourceQuantileLevel {N : ℕ} (i : Fin N) : ℝ :=
  ((N - 1 - i.val : ℕ) : ℝ) / (N : ℝ)

theorem empiricalCDF_nonnegative {N : ℕ} (values : Fin N → ℝ) (E : ℝ) :
    0 ≤ empiricalCDF values E := by
  unfold empiricalCDF
  positivity

theorem empiricalCDF_monotone {N : ℕ} (values : Fin N → ℝ) :
    Monotone (empiricalCDF values) := by
  intro x y hxy
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast Finset.card_le_card (show
      Finset.univ.filter (fun j => values j ≤ x) ⊆
        Finset.univ.filter (fun j => values j ≤ y) from by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2.trans hxy⟩)

theorem empiricalCDF_le_one {N : ℕ} (hN : 0 < N) (values : Fin N → ℝ) (E : ℝ) :
    empiricalCDF values E ≤ 1 := by
  have hcard : (Finset.univ.filter (fun j => values j ≤ E)).card ≤ N := by
    exact (Finset.card_filter_le _ _).trans_eq (by simp)
  apply (div_le_one (Nat.cast_pos.mpr hN)).mpr
  exact_mod_cast hcard

theorem empiricalCDF_below_ordered_value {N : ℕ} (values : Fin N → ℝ)
    (hsort : Antitone values) (i : Fin N) (E : ℝ) (hE : E < values i) :
    empiricalCDF values E ≤ sourceQuantileLevel i := by
  have hsub : Finset.univ.filter (fun j => values j ≤ E) ⊆ Finset.Ioi i := by
    intro j hj
    apply Finset.mem_Ioi.mpr
    have hval := (Finset.mem_filter.mp hj).2
    by_contra hij
    have hji : j ≤ i := le_of_not_gt hij
    exact (not_le_of_gt hE) ((hsort hji).trans hval)
  have hcard := Finset.card_le_card hsub
  rw [Fin.card_Ioi] at hcard
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hcard) (Nat.cast_nonneg N)

theorem quantileLevel_le_empiricalCDF_at_value {N : ℕ} (values : Fin N → ℝ)
    (hsort : Antitone values) (i : Fin N) :
    sourceQuantileLevel i ≤ empiricalCDF values (values i) := by
  have hsub : Finset.Ioi i ⊆ Finset.univ.filter (fun j => values j ≤ values i) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsort (Finset.mem_Ioi.mp hj).le⟩
  have hcard := Finset.card_le_card hsub
  rw [Fin.card_Ioi] at hcard
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hcard) (Nat.cast_nonneg N)

/-- Continuous CDF comparison gives the exact source rank, including ties. -/
theorem referenceCDF_at_ordered_value {N : ℕ} (values : Fin N → ℝ)
    (hsort : Antitone values) (F : ℝ → ℝ) (hF : Continuous F) (δ : ℝ)
    (hcompare : ∀ E, |empiricalCDF values E - F E| ≤ δ) (i : Fin N) :
    |F (values i) - sourceQuantileLevel i| ≤ δ := by
  have hlow : sourceQuantileLevel i - δ ≤ F (values i) := by
    have hh := (abs_le.mp (hcompare (values i))).2
    have hc := quantileLevel_le_empiricalCDF_at_value values hsort i
    linarith
  have hleft : ∀ᶠ E in 𝓝[<] (values i), F E ≤ sourceQuantileLevel i + δ := by
    filter_upwards [self_mem_nhdsWithin] with E hE
    have hc := empiricalCDF_below_ordered_value values hsort i E hE
    have hh := (abs_le.mp (hcompare E)).1
    linarith
  have hhigh : F (values i) ≤ sourceQuantileLevel i + δ :=
    le_of_tendsto (hF.continuousAt.mono_left nhdsWithin_le_nhds) hleft
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end SpectralConsequences
