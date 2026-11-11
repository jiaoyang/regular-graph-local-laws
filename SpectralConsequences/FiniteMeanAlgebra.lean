import SpectralConsequences.ExchangeableFinite
import LocalLaw.GraphConcentration

/-! # Complex finite-mean linearity and norm bounds -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
variable {E : Type*} [Fintype E]

theorem finiteComplexMean_eq_expectation (f:E→ℂ) :
    finiteComplexMean f=finiteExpectation (finiteUniformWeight E) f := by
  simp only [finiteComplexMean,finiteExpectation,finiteUniformWeight,Complex.real_smul,
    Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_natCast,one_div,Finset.mul_sum]

theorem finiteComplexMean_add (f g:E→ℂ) :
    finiteComplexMean (fun e=>f e+g e)=finiteComplexMean f+finiteComplexMean g := by
  simp only [finiteComplexMean_eq_expectation,finiteExpectation_add]

theorem finiteComplexMean_const_mul (a:ℂ) (f:E→ℂ) :
    finiteComplexMean (fun e=>a*f e)=a*finiteComplexMean f := by
  simp only [finiteComplexMean_eq_expectation,finiteExpectation_const_mul]

theorem finiteComplexMean_sub (f g:E→ℂ) :
    finiteComplexMean (fun e=>f e-g e)=finiteComplexMean f-finiteComplexMean g := by
  simp only [finiteComplexMean_eq_expectation,finiteExpectation_sub]

theorem finiteExpectation_norm_le (w:E→ℝ) (hw:∀e,0≤w e) (f:E→ℂ) :
    ‖finiteExpectation w f‖≤∑e,w e*‖f e‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro e _
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw e)]
  exact le_rfl

theorem finiteExpectation_norm_bound (w:E→ℝ) (hw:∀e,0≤w e) (f:E→ℂ)
    (M:ℝ) (hf:∀e,‖f e‖≤M) :
    ‖finiteExpectation w f‖≤M*(∑e,w e) := by
  apply (finiteExpectation_norm_le w hw f).trans
  calc
    _ ≤ ∑e,w e*M := Finset.sum_le_sum (fun e _=>mul_le_mul_of_nonneg_left (hf e) (hw e))
    _ = _ := by rw [←Finset.sum_mul,mul_comm]

/-- The omitted part is charged against its actual weighted probability. -/
theorem finiteExpectation_mask_difference (w:E→ℝ) (hw:∀e,0≤w e)
    (A:E→Prop) [DecidablePred A] (f:E→ℂ) (M:ℝ)
    (hf:∀e,¬A e→‖f e‖≤M) :
    ‖finiteExpectation w f-finiteExpectation w (fun e=>if A e then f e else 0)‖≤
      M*eventMass w (fun e=>¬A e) := by
  classical
  rw [←finiteExpectation_sub]
  apply (finiteExpectation_norm_le w hw _).trans
  unfold eventMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  by_cases hA:A e
  · simp [hA]
  · simp only [hA,if_false,not_false_eq_true,if_true,sub_zero]
    exact (mul_le_mul_of_nonneg_left (hf e hA) (hw e)).trans_eq (mul_comm _ _)

end SpectralConsequences
