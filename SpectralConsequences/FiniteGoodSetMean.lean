import SpectralConsequences.FiniteMeanAlgebra

/-! # Integrating a pointwise good-sample comparison

Both contributions are explicit: the genuine quadratic good-sample error
and the actual probability of the remaining samples. No desired mean bound
is supplied as an input.
-/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
variable {E:Type*} [Fintype E]

theorem finiteExpectation_comparison_of_good_event (w:E→ℝ) (hw:∀e,0≤w e)
    (htotal:∑e,w e≤1) (Good:E→Prop) [DecidablePred Good]
    (f g:E→ℂ) (err bad:ℝ) (herr:0≤err)
    (hgood:∀e,Good e→‖f e-g e‖≤err)
    (hbad:∀e,¬Good e→‖f e-g e‖≤bad) :
    ‖finiteExpectation w f-finiteExpectation w g‖≤
      err+bad*eventMass w (fun e=>¬Good e) := by
  classical
  rw [←finiteExpectation_sub]
  apply (finiteExpectation_norm_le w hw _).trans
  have hpoint (e:E):‖f e-g e‖≤err+(if Good e then 0 else bad):=by
    by_cases he:Good e
    · simpa only [he,if_true,add_zero] using hgood e he
    · simp only [he,if_false]
      exact (hbad e he).trans (le_add_of_nonneg_left herr)
  calc
    _ ≤ ∑e,w e*(err+(if Good e then 0 else bad)):=
      Finset.sum_le_sum (fun e _=>mul_le_mul_of_nonneg_left (hpoint e) (hw e))
    _ = err*(∑e,w e)+bad*eventMass w (fun e=>¬Good e):=by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,LocalLaw.eventMass]
      congr 1
      · apply Finset.sum_congr rfl
        intro e _
        ring
      · apply Finset.sum_congr rfl
        intro e _
        by_cases he:Good e <;>simp [he,mul_comm]
    _ ≤ _:=add_le_add_right (mul_le_of_le_one_right herr htotal) _

/-- Uniform finite means are the actual conditional means used in the graph
sampling fiber; nonemptiness supplies total mass one. -/
theorem finiteComplexMean_comparison_of_good_event [Nonempty E]
    (Good:E→Prop) [DecidablePred Good] (f g:E→ℂ) (err bad:ℝ) (herr:0≤err)
    (hgood:∀e,Good e→‖f e-g e‖≤err)
    (hbad:∀e,¬Good e→‖f e-g e‖≤bad) :
    ‖finiteComplexMean f-finiteComplexMean g‖≤
      err+bad*eventMass (finiteUniformWeight E) (fun e=>¬Good e) := by
  rw [finiteComplexMean_eq_expectation,finiteComplexMean_eq_expectation]
  exact finiteExpectation_comparison_of_good_event (finiteUniformWeight E)
    finiteUniformWeight_nonneg (le_of_eq finiteUniformWeight_total) Good f g err bad herr hgood hbad

end SpectralConsequences
