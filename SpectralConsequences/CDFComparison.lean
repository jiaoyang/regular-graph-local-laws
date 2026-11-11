import SpectralConsequences.SmoothedCDFComparison
import SpectralConsequences.KestenMcKayCDFLipschitz
import SpectralConsequences.EmpiricalSupport

/-! # A trace local law quantitatively controls the actual empirical CDF -/

open Set
noncomputable section
namespace SpectralConsequences
open LocalLaw

def cdfComparisonBudget (d : ℕ) (M η t h : ℝ) : ℝ :=
  (2*(M+2)/Real.pi)*t+2*η/Real.pi+
    2*kestenMcKayDensityCap d*h+2*(η/(Real.pi*h))

theorem empiricalCDF_error_of_smoothed_comparison {N : ℕ} (hN : 0 < N)
    (values : Fin N → ℝ) (d : ℕ) (hd : 3 ≤ d) (η h T E : ℝ)
    (hη : 0 < η) (hh : 0 < h)
    (hplus : |finitePoissonCDF values η (E+h)-kestenMcKayPoissonCDF d η (E+h)| ≤ T)
    (hminus : |finitePoissonCDF values η (E-h)-kestenMcKayPoissonCDF d η (E-h)| ≤ T) :
    |empiricalCDF values E-kestenMcKayCDF d E| ≤
      T+2*kestenMcKayDensityCap d*h+2*(η/(Real.pi*h)) := by
  have hfplus := empiricalCDF_le_smoothed_right hN values η h E hη hh
  have hfminus := smoothed_left_le_empiricalCDF hN values η h E hη hh
  have hrplus := kestenMcKay_smoothed_left_le_CDF d hd η h (E+2*h) hη hh
  rw [show E+2*h-h=E+h by ring] at hrplus
  have hrminus := kestenMcKayCDF_le_smoothed_right d hd η h (E-2*h) hη hh
  rw [show E-2*h+h=E-h by ring] at hrminus
  have hincplus := kestenMcKayCDF_increment_le d hd E (E+2*h) (by linarith)
  have hincminus := kestenMcKayCDF_increment_le d hd (E-2*h) E (by linarith)
  have hp := abs_le.mp hplus
  have hm := abs_le.mp hminus
  apply abs_le.mpr
  constructor
  · nlinarith only [hfminus,hrminus,hincminus,hm.1]
  · nlinarith only [hfplus,hrplus,hincplus,hp.2]

theorem empiricalCDF_error_of_trace {N : ℕ} (hN : 0 < N) (values : Fin N → ℝ)
    (d : ℕ) (hd : 3 ≤ d) (M η t h : ℝ) (hM : 2 ≤ M)
    (hη : 0 < η) (ht : 0 ≤ t) (hh : 0 < h) (hh1 : h ≤ 1)
    (hbox : ∀j,|values j| ≤ M)
    (htrace : ∀u ∈ Icc (-M-2) (M+2),
      ‖finiteStieltjes values ((u : ℂ)+(η : ℂ)*Complex.I)-
        kestenMcKayStieltjes d ((u : ℂ)+(η : ℂ)*Complex.I)‖ ≤ t) :
    ∀E,|empiricalCDF values E-kestenMcKayCDF d E| ≤ cdfComparisonBudget d M η t h := by
  have hbudget : 0 ≤ cdfComparisonBudget d M η t h := by
    have hK := (kestenMcKayDensityCap_positive d hd).le
    unfold cdfComparisonBudget
    positivity
  intro E
  by_cases hE : E ∈ Icc (-M) M
  · have hlow : ∀j,-M ≤ values j := fun j => (abs_le.mp (hbox j)).1
    have hp := smoothedCDF_error_on_box hN values d hd M η t (E+h) hM hη ht hlow
      (by constructor <;> linarith [hE.1,hE.2]) htrace
    have hm := smoothedCDF_error_on_box hN values d hd M η t (E-h) hM hη ht hlow
      (by constructor <;> linarith [hE.1,hE.2]) htrace
    exact empiricalCDF_error_of_smoothed_comparison hN values d hd η h
      ((2*(M+2)/Real.pi)*t+2*η/Real.pi) E hη hh hp hm
  · simp only [mem_Icc,not_and_or,not_le] at hE
    rcases hE with hlo|hhi
    · rw [empiricalCDF_eq_zero_of_lt_all values E
        (fun j => lt_of_lt_of_le hlo (abs_le.mp (hbox j)).1),
        kestenMcKayCDF_below d E (by linarith),sub_self,abs_zero]
      exact hbudget
    · rw [empiricalCDF_eq_one_of_all_le hN values E
        (fun j => ((abs_le.mp (hbox j)).2).trans hhi.le),
        kestenMcKayCDF_above d hd E (by linarith),sub_self,abs_zero]
      exact hbudget

theorem empiricalCDF_error_of_trace_sqrt {N : ℕ} (hN : 0 < N) (values : Fin N → ℝ)
    (d : ℕ) (hd : 3 ≤ d) (M η t : ℝ) (hM : 2 ≤ M)
    (hη : 0 < η) (hη1 : η ≤ 1) (ht : 0 ≤ t)
    (hbox : ∀j,|values j| ≤ M)
    (htrace : ∀u ∈ Icc (-M-2) (M+2),
      ‖finiteStieltjes values ((u : ℂ)+(η : ℂ)*Complex.I)-
        kestenMcKayStieltjes d ((u : ℂ)+(η : ℂ)*Complex.I)‖ ≤ t) :
    ∀E,|empiricalCDF values E-kestenMcKayCDF d E| ≤
      (2*(M+2)/Real.pi)*t+(2*kestenMcKayDensityCap d+4/Real.pi)*Real.sqrt η := by
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hs1 : Real.sqrt η ≤ 1 := Real.sqrt_le_one.mpr hη1
  have hsquare := Real.sq_sqrt hη.le
  have hηs : η ≤ Real.sqrt η := by nlinarith
  have hquot : η/(Real.pi*Real.sqrt η)=Real.sqrt η/Real.pi := by
    apply (div_eq_iff (mul_pos Real.pi_pos hs).ne').mpr
    field_simp [Real.pi_ne_zero]
    linear_combination -Real.pi*hsquare
  have hbudget : cdfComparisonBudget d M η t (Real.sqrt η) ≤
      (2*(M+2)/Real.pi)*t+(2*kestenMcKayDensityCap d+4/Real.pi)*Real.sqrt η := by
    unfold cdfComparisonBudget
    rw [hquot]
    have hm := div_le_div_of_nonneg_right hηs Real.pi_pos.le
    calc
      _=(2*(M+2)/Real.pi)*t+2*(η/Real.pi)+2*kestenMcKayDensityCap d*Real.sqrt η+
          2*(Real.sqrt η/Real.pi) := by ring
      _≤(2*(M+2)/Real.pi)*t+2*(Real.sqrt η/Real.pi)+2*kestenMcKayDensityCap d*Real.sqrt η+
          2*(Real.sqrt η/Real.pi) := by
        gcongr
      _=_ := by ring
  intro E
  exact (empiricalCDF_error_of_trace hN values d hd M η t (Real.sqrt η) hM hη ht hs hs1 hbox htrace E).trans hbudget

end SpectralConsequences
