import SpectralConsequences.FiniteMeanAlgebra

/-! Charging a genuine exceptional event with bounds only on nonzero support. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem finiteExpectation_event_product_bound {X:Type*}[Fintype X]
    (w:X→ℝ) (hw:∀x,0≤w x) (A P:X→Prop) [DecidablePred A] [DecidablePred P]
    (f test:X→ℂ) (C M:ℝ) (hC:0≤C) (hM:0≤M)
    (hf:∀x,w x≠0→A x→‖f x‖≤C) (ht:∀x,A x→‖test x‖≤M):
    ‖finiteExpectation w (fun x=>if A x∧P x then f x*test x else 0)‖≤C*M*eventMass w P:=by
  classical
  apply (finiteExpectation_norm_le w hw _).trans
  rw [eventMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have hwxnonneg:=hw x
  by_cases hpx:P x
  · by_cases hax:A x
    · by_cases hwx:w x=0
      · simp [hpx,hax,hwx]
      · simp only [hpx,hax,and_self,if_true,norm_mul]
        have hh:=mul_le_mul (hf x hwx hax) (ht x hax) (norm_nonneg _) hC
        exact (mul_le_mul_of_nonneg_left hh (hw x)).trans_eq (by ring)
    · simp only [hpx,hax,false_and,if_false,if_true,norm_zero,mul_zero]
      positivity
  · simp [hpx]

end SpectralConsequences
