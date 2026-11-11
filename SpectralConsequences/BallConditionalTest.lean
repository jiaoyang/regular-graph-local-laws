import SpectralConsequences.CanonicalBallResampling

/-! Graph-measurable test functions and cutoffs factor through the actual
ball conditional expectation, followed by its exact weighted norm bound. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance ballConditionalTestDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem ballLabelledConditionalMean_mul_test (N d:ℕ)(o:Fin N)(ell:ℕ)
    (f:BallLabelledSpace N d→ℂ)(test:RegularGraph N d→ℂ)(g:RegularGraph N d):
    ballLabelledConditionalMean N d o ell (fun ω=>f ω*test (ballLabelledProject ω)) g=
      ballLabelledConditionalMean N d o ell f g*test g:=by
  unfold ballLabelledConditionalMean globalLabelledConditionalMean
  simp only [ballLabelledProject,canonicalGlobalLabelledState_project]
  unfold finiteComplexMean
  simp only [Complex.real_smul]
  rw [←Finset.sum_mul]
  ring

theorem ballLabelledConditionalMean_cutoff_mul_test (N d:ℕ)(o:Fin N)(ell:ℕ)
    (A:RegularGraph N d→Prop)(f:BallLabelledSpace N d→ℂ)(test:RegularGraph N d→ℂ)
    (g:RegularGraph N d):
    ballLabelledConditionalMean N d o ell
      (fun ω=>if A (ballLabelledProject ω) then f ω*test (ballLabelledProject ω) else 0) g=
      if A g then ballLabelledConditionalMean N d o ell f g*test g else 0:=by
  by_cases hA:A g
  · have heq:ballLabelledConditionalMean N d o ell
        (fun ω=>if A (ballLabelledProject ω) then f ω*test (ballLabelledProject ω) else 0) g=
        ballLabelledConditionalMean N d o ell (fun ω=>f ω*test (ballLabelledProject ω)) g:=by
      unfold ballLabelledConditionalMean globalLabelledConditionalMean
      simp only [ballLabelledProject,canonicalGlobalLabelledState_project,hA,if_true]
    rw [heq,ballLabelledConditionalMean_mul_test,if_pos hA]
  · unfold ballLabelledConditionalMean globalLabelledConditionalMean
    simp only [ballLabelledProject,canonicalGlobalLabelledState_project,hA,if_false,
      finiteComplexMean,Finset.sum_const_zero,smul_zero]

theorem ball_labelled_cutoff_test_disintegration (N d:ℕ)(o:Fin N)(ell:ℕ)
    (A:RegularGraph N d→Prop)(f:BallLabelledSpace N d→ℂ)(test:RegularGraph N d→ℂ):
    finiteExpectation (ballLabelledWeight N d o ell)
      (fun ω=>if A (ballLabelledProject ω) then f ω*test (ballLabelledProject ω) else 0)=
      finiteExpectation (RegularGraph.weight (N:=N) (d:=d))
        (fun g=>if A g then ballLabelledConditionalMean N d o ell f g*test g else 0):=by
  rw [ball_labelled_complex_disintegration]
  congr 1
  funext g
  exact ballLabelledConditionalMean_cutoff_mul_test N d o ell A f test g

theorem ball_labelled_conditional_test_norm (N d:ℕ)(o:Fin N)(ell:ℕ)
    (A:RegularGraph N d→Prop)(f:BallLabelledSpace N d→ℂ)(test:RegularGraph N d→ℂ)
    (B:RegularGraph N d→ℝ)
    (hbound:∀g,A g→‖ballLabelledConditionalMean N d o ell f g‖≤B g):
    ‖finiteExpectation (ballLabelledWeight N d o ell)
      (fun ω=>if A (ballLabelledProject ω) then f ω*test (ballLabelledProject ω) else 0)‖≤
      ∑g:RegularGraph N d,if A g then RegularGraph.weight g*B g*‖test g‖ else 0:=by
  rw [ball_labelled_cutoff_test_disintegration]
  apply (finiteExpectation_norm_le RegularGraph.weight RegularGraph.weight_nonnegative _).trans
  apply Finset.sum_le_sum
  intro g _
  by_cases hA:A g
  · simp only [hA,if_true,norm_mul]
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hbound g hA) (norm_nonneg _))
      (RegularGraph.weight_nonnegative g)).trans_eq (by ring)
  · simp only [hA,if_false,norm_zero,mul_zero]
    exact le_rfl

end SpectralConsequences
