import LocalLaw.SelfAdjointResolventLimit

/-! Definition 2.6's printed positive constant diagonal lower bound on ALL
of C+ is impossible. This is a proved obstruction, not a proof assumption.
The relative-|md| lower bound used by the reference classes avoids it. -/
open scoped ENNReal
noncomputable section
namespace SpectralConsequences
open LocalLaw
variable {V : Type} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

theorem infiniteGreen_norm_le (d : ℕ) (hD : ∀v,G.degree v≤d)
    (z : ℂ) (hz : 0<z.im) (i j : V) :
    ‖G.infiniteGreen d hD z i j‖≤1/z.im := by
  have he := lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0)
    (G.infiniteGreenOperator d hD z (lp.single 2 j 1)) i
  have hb := physicalResolvent_apply_norm_bound (G.normalizedOperator d hD)
    (G.normalizedOperator_selfAdjoint d hD) z hz (lp.single 2 j (1:ℂ))
  rw [lp.norm_single (by norm_num : 0<(2:ℝ≥0∞)),norm_one] at hb
  exact he.trans hb

theorem infiniteGreen_arbitrarily_small (d : ℕ) (hD : ∀v,G.degree v≤d)
    (i j : V) (ε : ℝ) (hε : 0<ε) :
    ∃z:ℂ,0<z.im ∧ ‖G.infiniteGreen d hD z i j‖<ε := by
  let z : ℂ := ⟨0,2/ε⟩
  have hz : 0<z.im := by dsimp [z]; positivity
  refine ⟨z,hz,?_⟩
  have hb := infiniteGreen_norm_le G d hD z hz i j
  have he : 1/z.im=ε/2 := by dsimp [z]; field_simp
  rw [he] at hb
  linarith

theorem no_global_positive_diagonal_lower_bound (d : ℕ) (hD : ∀v,G.degree v≤d)
    (i : V) :
    ¬∃a:ℝ,0<a ∧ ∀z:ℂ,0<z.im→a≤‖G.infiniteGreen d hD z i i‖ := by
  rintro ⟨a,ha,h⟩
  obtain ⟨z,hz,hsmall⟩ := infiniteGreen_arbitrarily_small G d hD i i a ha
  exact (not_lt_of_ge (h z hz)) hsmall

end SpectralConsequences
#print axioms SpectralConsequences.no_global_positive_diagonal_lower_bound
