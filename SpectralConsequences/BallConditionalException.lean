import SpectralConsequences.BallConditionalTest

/-! Conditional graph-dependent estimates with an all-power auxiliary loss. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance ballConditionalExceptionDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem ball_conditional_test_with_exception (N d:ℕ) (o:Fin N) (ell:ℕ)
    (A Aux:RegularGraph N d→Prop) (f:BallLabelledSpace N d→ℂ) (test:RegularGraph N d→ℂ)
    (B C M:ℝ) (hB:0≤B) (hC:0≤C) (hM:0≤M)
    (hgood:∀g,A g→Aux g→‖ballLabelledConditionalMean N d o ell f g‖≤B)
    (hbad:∀g,A g→¬Aux g→‖ballLabelledConditionalMean N d o ell f g‖≤C)
    (htest:∀g,A g→‖test g‖≤M):
    ‖finiteExpectation (ballLabelledWeight N d o ell) (fun ω=>
      if A (ballLabelledProject ω) then f ω*test (ballLabelledProject ω) else 0)‖≤
      B*(∑g:RegularGraph N d,if A g then RegularGraph.weight g*‖test g‖ else 0)+
      C*M*eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>¬Aux g):=by
  have hb:∀g,A g→‖ballLabelledConditionalMean N d o ell f g‖ ≤ (if Aux g then B else C):=by
    intro g ha
    by_cases hg:Aux g
    · simpa only [hg,if_true] using hgood g ha hg
    · simpa only [hg,if_false] using hbad g ha hg
  apply (ball_labelled_conditional_test_norm N d o ell A f test
    (fun g=>if Aux g then B else C) hb).trans
  simp only [eventMass,Finset.mul_sum]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g _
  have hw:=RegularGraph.weight_nonnegative g
  by_cases ha:A g
  · by_cases hg:Aux g
    · simp only [ha,hg,not_true_eq_false,if_true,if_false,mul_zero,add_zero]
      ring_nf
      exact le_rfl
    · simp only [ha,hg,not_false_eq_true,if_true,if_false]
      have ht:=mul_le_mul_of_nonneg_left (htest g ha) (mul_nonneg hw hC)
      nlinarith [mul_nonneg (mul_nonneg hB hw) (norm_nonneg (test g))]
  · by_cases hg:Aux g
    · simp [ha,hg]
    · simp only [ha,hg,not_false_eq_true,if_false,if_true,mul_zero,zero_add]
      positivity

end SpectralConsequences
