import SpectralConsequences.CDFComparison
import SpectralConsequences.KestenMcKayQuantiles
import SpectralConsequences.FiniteGridExclusion

/-! # Quantile rigidity from counting-height and exterior-grid resolvents

This deterministic theorem has actual CDF/quantile/Poisson identifications.
The source graph theorem separately proves its two resolvent estimates.
-/

open Set
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem rigidity_of_two_resolvent_bounds {N : ℕ} (hN : 0 < N)
    (values : Fin N → ℝ) (hsort : Antitone values) (d : ℕ) (hd : 3 ≤ d)
    (M η t ηe Δ : ℝ) (hM : 2 ≤ M) (hη : 0 < η) (hη1 : η ≤ 1)
    (ht : 0 ≤ t) (hηe : 0 < ηe) (hΔ : 0 ≤ Δ)
    (removed : Finset (Fin N)) (grid : Finset ℝ) (hbox : ∀j,|values j| ≤ M)
    (htrace : ∀u ∈ Icc (-M-2) (M+2),
      ‖finiteStieltjes values ((u : ℂ)+(η : ℂ)*Complex.I)-
        kestenMcKayStieltjes d ((u : ℂ)+(η : ℂ)*Complex.I)‖ ≤ t)
    (hcover : ∀x,(-M ≤ x ∧ x < -2-Δ) ∨ (2+Δ < x ∧ x ≤ M) →
      ∃ E ∈ grid,|x-E| ≤ ηe)
    (hexterior : ∀E ∈ grid,
      (correctedFiniteStieltjes values removed ((E : ℂ)+(ηe : ℂ)*Complex.I)).im <
        1/(2*(N : ℝ)*ηe)) :
    ∀i,i ∉ removed → |values i-classicalLocation d hd i| ≤
      Δ+(12*Real.pi*((2*(M+2)/Real.pi)*t+
        (2*kestenMcKayDensityCap d+4/Real.pi)*Real.sqrt η))^(2/3 : ℝ) := by
  let δ := (2*(M+2)/Real.pi)*t+(2*kestenMcKayDensityCap d+4/Real.pi)*Real.sqrt η
  have hδ : 0 ≤ δ := by
    have hK := (kestenMcKayDensityCap_positive d hd).le
    dsimp only [δ]
    positivity
  have hCDF : ∀E,|empiricalCDF values E-kestenMcKayCDF d E| ≤ δ :=
    empiricalCDF_error_of_trace_sqrt hN values d hd M η t hM hη hη1 ht hbox htrace
  have hconf := finite_grid_confinement values removed hN M (-2) 2 Δ ηe hηe grid
    (fun j => abs_le.mp (hbox j)) hcover hexterior
  intro i hi
  have hh := (kestenMcKaySquareRootCDF d hd).rigidity_of_cdf_and_confinement
    values hsort δ Δ hδ hΔ hCDF i (hconf i hi).1 (hconf i hi).2
  change |values i-classicalLocation d hd i| ≤ Δ+(δ/(1/(12*Real.pi)))^(2/3 : ℝ) at hh
  have heq : δ/(1/(12*Real.pi))=12*Real.pi*δ := by
    rw [one_div,div_inv_eq_mul]
    ring
  rw [heq] at hh
  exact hh

theorem hermitian_rigidity_of_two_resolvent_bounds {N : ℕ} (hN : 0 < N)
    (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian) (d : ℕ) (hd : 3 ≤ d)
    (M η t ηe Δ : ℝ) (hM : 2 ≤ M) (hη : 0 < η) (hη1 : η ≤ 1)
    (ht : 0 ≤ t) (hηe : 0 < ηe) (hΔ : 0 ≤ Δ)
    (removed : Finset (Fin N)) (grid : Finset ℝ)
    (hbox : ∀j,|sortedEigenvalues hH j| ≤ M)
    (htrace : ∀u ∈ Icc (-M-2) (M+2),
      ‖empiricalTransform H ((u : ℂ)+(η : ℂ)*Complex.I)-
        kestenMcKayStieltjes d ((u : ℂ)+(η : ℂ)*Complex.I)‖ ≤ t)
    (hcover : ∀x,(-M ≤ x ∧ x < -2-Δ) ∨ (2+Δ < x ∧ x ≤ M) →
      ∃ E ∈ grid,|x-E| ≤ ηe)
    (hexterior : ∀E ∈ grid,
      (correctedFiniteStieltjes (sortedEigenvalues hH) removed ((E : ℂ)+(ηe : ℂ)*Complex.I)).im <
        1/(2*(N : ℝ)*ηe)) :
    ∀i,i ∉ removed → |sortedEigenvalues hH i-classicalLocation d hd i| ≤
      Δ+(12*Real.pi*((2*(M+2)/Real.pi)*t+
        (2*kestenMcKayDensityCap d+4/Real.pi)*Real.sqrt η))^(2/3 : ℝ) := by
  apply rigidity_of_two_resolvent_bounds hN (sortedEigenvalues hH) (sortedEigenvalues_antitone hH)
    d hd M η t ηe Δ hM hη hη1 ht hηe hΔ removed grid hbox _ hcover hexterior
  intro u hu
  have hz : 0 < ((u : ℂ)+(η : ℂ)*Complex.I).im := by simpa using hη
  rw [←empiricalTransform_eq_finiteStieltjes H hH _ hz]
  exact htrace u hu

end SpectralConsequences
