import SpectralConsequences.ProductCoordinateMeans
import SpectralConsequences.FiniteMeanAlgebra

/-! # Integrating the exact finite boundary Schur expansion -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
variable {E I:Type*} [Fintype E] [Fintype I]

theorem finiteComplexMean_sum (f:I→E→ℂ) :
    finiteComplexMean (fun e:E=>∑i:I,f i e)=∑i:I,finiteComplexMean (f i) := by
  simp only [finiteComplexMean_eq_expectation,finiteExpectation,Finset.mul_sum]
  exact Finset.sum_comm

theorem finiteComplexMean_norm_bound [Nonempty E] (f:E→ℂ) (R:ℝ)
    (hR:∀e,‖f e‖≤R) : ‖finiteComplexMean f‖≤R := by
  rw [finiteComplexMean_eq_expectation]
  have hh:=finiteExpectation_norm_bound (finiteUniformWeight E) finiteUniformWeight_nonneg f R hR
  simpa only [finiteUniformWeight_total,mul_one] using hh

theorem finite_boundary_mean_aggregation [Nonempty E] [DecidableEq I]
    (f rem:E→ℂ) (D:E→I→I→ℂ) (w:I→ℂ) (reference c θ:ℂ) (err R:ℝ)
    (hidentity:∀e,f e-reference=c*(∑i:I,∑j:I,w i*w j*D e i j)+rem e)
    (hdiag:∀i,‖finiteComplexMean (fun e=>D e i i)‖≤err)
    (hoff:∀i j,i≠j→‖finiteComplexMean (fun e=>D e i j)-θ‖≤err)
    (hrem:∀e,‖rem e‖≤R) :
    ‖finiteComplexMean f-reference-c*θ*(∑i:I,∑j:I,if i=j then 0 else w i*w j)‖≤
      ‖c‖*err*(∑i:I,‖w i‖)^2+R := by
  have hm:finiteComplexMean f-reference=
      c*(∑i:I,∑j:I,w i*w j*finiteComplexMean (fun e=>D e i j))+finiteComplexMean rem:=by
    rw [←finiteComplexMean_const (E:=E) reference,←finiteComplexMean_sub]
    simp_rw [hidentity,finiteComplexMean_add,finiteComplexMean_const_mul,finiteComplexMean_sum]
    simp_rw [finiteComplexMean_const_mul]
  let A:I→I→ℂ:=fun i j=>finiteComplexMean (fun e=>D e i j)-(if i=j then 0 else θ)
  have hA:∀i j,‖A i j‖≤err:=by
    intro i j
    by_cases hij:i=j
    · subst j
      simpa only [A,if_true,sub_zero] using hdiag i
    · simpa only [A,hij,if_false] using hoff i j hij
  have hsum: (∑i:I,∑j:I,w i*w j*finiteComplexMean (fun e=>D e i j))-
      θ*(∑i:I,∑j:I,if i=j then 0 else w i*w j)=∑i:I,∑j:I,w i*w j*A i j:=by
    simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij:i=j <;>simp only [A,hij,if_true,if_false] <;>ring
  have hn:‖∑i:I,∑j:I,w i*w j*A i j‖≤err*(∑i:I,‖w i‖)^2:=by
    apply ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _=>norm_sum_le _ _))).trans
    calc
      _ ≤ ∑i:I,∑j:I,‖w i‖*‖w j‖*err:=by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul,norm_mul]
        exact mul_le_mul_of_nonneg_left (hA i j) (by positivity)
      _ = _:=by
        rw [pow_two]
        simp only [Finset.mul_sum,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hid:finiteComplexMean f-reference-c*θ*(∑i:I,∑j:I,if i=j then 0 else w i*w j)=
      c*(∑i:I,∑j:I,w i*w j*A i j)+finiteComplexMean rem:=by
    rw [hm,←hsum]
    ring
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add
    (by rw [norm_mul];exact (mul_le_mul_of_nonneg_left hn (norm_nonneg c)).trans_eq (by ring))
    (finiteComplexMean_norm_bound rem R hrem))

end SpectralConsequences
