import SpectralConsequences.PoissonTraceBounds

/-! # Trace comparison bounds actual smoothed empirical and reference CDFs -/

open Set
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem smoothedCDF_error_on_box {N : ℕ} (hN : 0 < N) (values : Fin N → ℝ)
    (d : ℕ) (hd : 3 ≤ d) (M η t E : ℝ) (hM : 2 ≤ M) (hη : 0 < η) (ht : 0 ≤ t)
    (hlower : ∀j,-M ≤ values j) (hE : E ∈ Icc (-M-1) (M+1))
    (htrace : ∀u ∈ Icc (-M-2) (M+2),
      ‖finiteStieltjes values ((u : ℂ)+(η : ℂ)*Complex.I)-
        kestenMcKayStieltjes d ((u : ℂ)+(η : ℂ)*Complex.I)‖ ≤ t) :
    |finitePoissonCDF values η E-kestenMcKayPoissonCDF d η E| ≤
      (2*(M+2)/Real.pi)*t+2*η/Real.pi := by
  let a := -M-1
  have haE : a ≤ E := hE.1
  have hinc := smoothed_increment_error values d hd η a E t hη haE (by
    intro u hu
    exact htrace u ⟨by dsimp only [a] at hu;linarith [hu.1],by linarith [hu.2,hE.2]⟩)
  have hlen : E-a ≤ 2*(M+2) := by dsimp only [a];linarith [hE.2]
  have hscaled := mul_le_mul_of_nonneg_left hlen (div_nonneg ht Real.pi_pos.le)
  have hinc' : |(finitePoissonCDF values η E-finitePoissonCDF values η a)-
      (kestenMcKayPoissonCDF d η E-kestenMcKayPoissonCDF d η a)| ≤
      (2*(M+2)/Real.pi)*t := hinc.trans (hscaled.trans_eq (by ring))
  have hf0 := finitePoissonCDF_nonnegative values η a
  have hg0 := kestenMcKayPoissonCDF_nonnegative d hd η a
  have hft : finitePoissonCDF values η a ≤ η/Real.pi :=
    finitePoissonCDF_left_tail hN values M η hη hlower
  have hgt : kestenMcKayPoissonCDF d η a ≤ η/Real.pi :=
    kestenMcKayPoissonCDF_left_tail d hd M η hM hη
  have hleft : |finitePoissonCDF values η a-kestenMcKayPoissonCDF d η a| ≤ 2*η/Real.pi := by
    have hh := abs_sub_le (finitePoissonCDF values η a) 0 (kestenMcKayPoissonCDF d η a)
    rw [sub_zero,zero_sub,abs_neg,abs_of_nonneg hf0,abs_of_nonneg hg0] at hh
    exact hh.trans ((add_le_add hft hgt).trans_eq (by ring))
  have heq : finitePoissonCDF values η E-kestenMcKayPoissonCDF d η E=
      ((finitePoissonCDF values η E-finitePoissonCDF values η a)-
        (kestenMcKayPoissonCDF d η E-kestenMcKayPoissonCDF d η a))+
        (finitePoissonCDF values η a-kestenMcKayPoissonCDF d η a) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hinc' hleft)

end SpectralConsequences
