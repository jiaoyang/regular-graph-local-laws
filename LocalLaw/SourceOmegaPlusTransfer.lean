import LocalLaw.SourceDeletionComparison
import LocalLaw.GraphExcessSurgery

/-!
# Original weak source event implies the actual enlarged source event

Proposition 5.1 is assembled on the actual graph and selected nonresonant
radius. Deleted approximation, Schur absorption and all localization budgets
are proved; they are not fields in the event implication.
-/

open Filter
noncomputable section
namespace LocalLaw

namespace RegularGraph

/-- Source Proposition 5.1 with an explicit sufficient fixed choice of C1.
It uses the original structural radius, without a deleted-regularity premise. -/
theorem eventually_sourceOmega_subset_sourceOmegaPlus (a b d : ℕ) (c β B C1 : ℝ) (Cq : ℕ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hB : 0 ≤ B)
    (hC1 : 1 ≤ C1) (hCdel : sourceDeletionConstant d β B ≤ C1) (hCq : finiteOmega d ≤ Cq) :
    ∀ᶠ N : ℕ in atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ) (badCount : ℕ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      g.SourceOmega a (logarithmicRadius β d N) (logarithmicRadius (c / 4) d N)
        (finiteOmega d) badCount z →
      g.SourceOmegaPlus a (logarithmicRadius β d N) (logarithmicRadius (c / 4) d N)
        (actualCavityDepth a d N z - 1) (finiteOmega d) Cq badCount C1 o z := by
  have hdepthLarge := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_sourceDeletionBounds a b d β B ha hb hd hβ hB,
    eventually_source_radius_hierarchy a d c β hd hc hβ hβc, hdepthLarge]
    with N hbudgets hradii hdepthLarge
  intro g o z badCount hz hzB hfloor hOmega
  let r := logarithmicRadius β d N
  let R := logarithmicRadius (c / 4) d N
  let ell := actualCavityDepth a d N z - 1
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N r z
  have S := hbudgets z hz hfloor
  have hL : 1 ≤ L := S.localization.log_one
  have hLp : 0 < L := by linarith
  have hε : 0 ≤ ε := S.localization.error_nonnegative
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepthLarge).2
  have hr : 1 ≤ r := by have hh := hradii.2.1; dsimp only [r]; omega
  have hmargin : 6 * (ell + r) + 2 ≤ R := by
    have hh := hradii.2.1
    have he := hradii.1
    dsimp only [r, R] at *
    omega
  have hprior : ‖g.Q z - semicircleRoot z‖ ≤ scalarScale (spectralScale z) ε := hOmega.2.1
  have hΨ : 0 ≤ scalarScale (spectralScale z) ε := scalarScale_nonneg hε
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro v
      exact (graphBallExcess_mono_radius g.graph v (Nat.div_le_self R 8)).trans (hOmega.1.1 v)
    · intro v
      exact ((graphBallExcess_mono_radius g.graph v (Nat.div_le_self R 2)).trans (hOmega.1.1 v)).trans hCq
    · exact hOmega.1.2.trans (Nat.le_mul_of_pos_left _ (by norm_num))
  · exact hprior.trans (le_mul_of_one_le_left hΨ hC1)
  · intro i j
    apply (hOmega.2.2 i j).trans
    apply (le_div_iff₀ hLp).mpr
    have hpow : L ≤ L ^ 4 := by simpa only [pow_one] using pow_le_pow_right₀ hL (show 1 ≤ 4 by norm_num)
    have hh := (mul_le_mul_of_nonneg_left hpow hε).trans S.localization.error_scaled
    exact hh.trans hC1
  · dsimp only
    intro i j
    have hdel := g.source_deleted_comparison S hd hβ.le R hr hmargin hOmega.1.1
      (g.Q z) hz (g.Q_im_nonnegative z hz) hzB hprior hOmega.2.2 o i j
    apply hdel.trans
    change sourceDeletionConstant d β B * L ^ 3 * ε ≤ C1 * (L ^ 3 * ε)
    have hh := mul_le_mul_of_nonneg_right hCdel (show 0 ≤ L ^ 3 * ε by positivity)
    calc
      _ = sourceDeletionConstant d β B * (L ^ 3 * ε) := by ring
      _ ≤ C1 * (L ^ 3 * ε) := hh

end RegularGraph
end LocalLaw
