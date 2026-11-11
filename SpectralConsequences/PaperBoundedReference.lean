import SpectralConsequences.AllCoreReferenceThreshold

/-! The corrected global reference lower bound implies the usual constant
upper and lower diagonal bounds on every fixed bounded spectral region. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem allCore_reference_bounded_diagonal (d ω : ℕ) (hd : 3≤d)
    (hclass : AllCoreReferenceThreshold d ω (by omega)) :
    ∃C:ℝ,1≤C ∧ ∀(V:Type)[DecidableEq V](g:AllCoreGraph V d),
      g.graph.Connected → g.HereditaryBudget ω → ∀z:ℂ,0<z.im → ∀B:ℝ,‖z‖≤B →
        ∀i:V,(1/(B+2))/C≤‖g.green (by omega) z i i‖ ∧
          ‖g.green (by omega) z i i‖≤C := by
  obtain ⟨C,hC,h⟩ := hclass
  refine ⟨C,hC,?_⟩
  intro V _ g hconn hbudget z hz B hB i
  have href := h V g hconn hbudget z hz
  constructor
  · exact (div_le_div_of_nonneg_right
      (kestenMcKay_bounded_norm_lower d hd z hz B hB) (by linarith : 0≤C)).trans
        (href.2.2 i)
  · simpa only [SimpleGraph.dist_self,pow_zero,mul_one] using href.1 i i

end SpectralConsequences
#print axioms SpectralConsequences.allCore_reference_bounded_diagonal
