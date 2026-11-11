import LocalLaw.ComponentFiniteLocalization
import LocalLaw.LocalizationWeakBudgets

/-!
# Weak-prior localization for actual disconnected finite models

All component reference classes, pair-disconnection cases and five feedback
inequalities are discharged. Only a weak prior, an explicit error/diameter
scale, and a fixed large-L condition remain for source-parameter realization.
-/

noncomputable section
namespace LocalLaw
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem componentwise_weak_pair_localization (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hbudget : g.ComponentFiniteReferenceBudget)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (Bcap : ℝ) (hBcap : ‖z‖ ≤ Bcap)
    (ε L A : ℝ) (hε : 0 ≤ ε) (hL : 1 ≤ L) (hA : 0 ≤ A) (hcap : ε * L ^ 4 ≤ 1)
    (hprior : ‖q - semicircleRoot z‖ ≤ scalarScale (spectralScale z) ε)
    (R r : ℕ) (hR : ∀ a b, g.graph.dist a b ≤ R)
    (hRlog : (R : ℝ) + 1 ≤ A * L) (hrlog : ((4 * r + 1 : ℕ) + 1 : ℝ) ≤ A * L)
    (hlarge : localizationBudgetConstant d Bcap A ≤ L)
    (htail : physicalTransfer d z ^ (2 * r) ≤ ε) (i j : V) :
    ‖g.extensionGreen q z i j - g.P r z q i j‖ ≤ localizationWeakConstant d Bcap A * L * ε := by
  obtain ⟨smallG, smallS, smallOutside, smallCavity, smallOrdinary⟩ :=
    weak_localization_feedback_budgets d hd z q hz Bcap ε L A hε hL hA hcap hprior
      R (4 * r + 1) hRlog hrlog hlarge
  have hlocal := g.componentwise_pair_localization hd hbudget q z hz hq Bcap hBcap R r hR
    smallG smallS smallOutside smallCavity smallOrdinary i j
  have hLpow : 1 ≤ L ^ 4 := one_le_pow₀ hL
  have hεone : ε ≤ 1 := (by nlinarith only [mul_le_mul_of_nonneg_left hLpow hε, hcap])
  exact hlocal.trans (localization_expression_weak_rate d hd z q hz Bcap ε L A hε hεone hL hA
    hprior R r hRlog htail)

end DeficientGraph
end LocalLaw
