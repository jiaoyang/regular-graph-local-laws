import SpectralConsequences.SourceSpectralBox
import SpectralConsequences.FiniteGridExclusion

/-! # Subtracting exactly one actual trivial mode

The remaining positive measure still counts every other eigenvalue index,
including any additional occurrence of the regular constant eigenvalue.
-/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
namespace RegularGraph
variable {N d:ℕ}

def correctedSourceTrace (g:LocalLaw.RegularGraph N d) (z:ℂ):ℂ:=
  empiricalTransform g.H z-(N:ℂ)⁻¹*((regularSpectralRadius d:ℂ)-z)⁻¹

theorem correctedSourceTrace_eq_positive_sum (g:LocalLaw.RegularGraph N d) (hN:0<N)
    (z:ℂ) (hz:0<z.im) :
    correctedSourceTrace g z=correctedFiniteStieltjes (sortedEigenvalues g.H_hermitian) {⟨0,hN⟩} z := by
  rw [correctedFiniteStieltjes_eq_sub,←empiricalTransform_eq_finiteStieltjes g.H g.H_hermitian z hz]
  simp only[Finset.sum_singleton,sorted_top_eigenvalue g hN]
  rfl

theorem correctedSourceTrace_im (g:LocalLaw.RegularGraph N d) (hN:0<N)
    (E η:ℝ) (hη:0<η) :
    (correctedSourceTrace g ((E:ℂ)+(η:ℂ)*Complex.I)).im=
      (N:ℝ)⁻¹*∑i∈({⟨0,hN⟩}:Finset (Fin N))ᶜ,
        η/((sortedEigenvalues g.H_hermitian i-E)^2+η^2) := by
  rw [correctedSourceTrace_eq_positive_sum g hN _ (by simpa using hη),correctedFiniteStieltjes_im]

end RegularGraph
end SpectralConsequences
